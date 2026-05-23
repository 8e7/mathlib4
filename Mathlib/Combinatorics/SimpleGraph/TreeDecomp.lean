/-
Copyright (c) 2026 Justin Lai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justin Lai
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Circulant
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Separator
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Combinatorics.SimpleGraph.Star
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Tactic.ENatToNat

/-!
# Tree Decompositions and Tree Width

This file defines tree decompositions on simple graphs and the treewidth.

## Main definitions

* `SimpleGraph.TreeDecomp` is a tree decomposition of a simple graph.
* `TreeDecomp.ewidth` is the extended width of the tree decomposition. `TreeDecomp.width` is the
  ℕ-valued version, and is equivalent to `ewidth` when there is `[Finite V]`.
* `SimpleGraph.hasTreeDecomp n` is a predicate that a simple graph has a tree decomposition of width
  at most n.
* `SimpleGraph.etreeWidth` is the extended tree width of a simple graph. `SimpleGraph.treeWidth` is
  the ℕ-valued version.

## Main statements

* `treeWidth_le_card` shows that a finite graph must have finite treewidth.
* `treewidth_top` shows that the complete graph with finite vertices has treewidth `card V - 1`.
* `adhesion_imp_separator` proves that the adhesion set (the intersection of two adjacent bags) is
  a graph separator for vertices on different sides of the tree.

## References

* [R. Diestel **Graph Theory**
  https://doi.org/10.1007/978-3-662-70107-2][diestel2025]

## Tags
tree decomposition, treewidth

-/

@[expose] public section

open Finset Fintype

namespace SimpleGraph

universe u v
variable {V : Type u} {V' : Type v}
variable {G : SimpleGraph V} {G' : SimpleGraph V'}

/-! ## Tree decompositions -/

section TreeDecomp

/-- A tree decomposition of a simple graph `G` is a tree `T` indexed by a type
`W`, together with a bag `𝓧 w : Finset V` assigned to each `w : W`, such that
every edge of `G` lies in some bag and the bags containing any fixed vertex form
a connected subgraph of `T`. -/
structure TreeDecomp (G : SimpleGraph V) where
  /-- The type of bags in the tree. -/
  W : Type
  /-- The set of vertices in each bag. -/
  𝓧 : W → Finset V
  /-- The graph adjacency relation of bags. -/
  T : SimpleGraph W
  /-- T must be a tree. -/
  isTree : IsTree T
  /-- All vertices in G must appear in some bag. -/
  vertexCover : ∀ v : V, ∃ w : W, v ∈ 𝓧 w
  /-- For any edge (u, v) in G, there is a bag containing both u and v. -/
  edgeCover ⦃u v : V⦄ : G.Adj u v → ∃ w : W, u ∈ 𝓧 w ∧ v ∈ 𝓧 w
  /-- For any vertex v in G, the set of bags that contain v is preconnected. -/
  connectedBags : ∀ v : V, (T.induce ({w | v ∈ 𝓧 w})).Preconnected

instance (t : G.TreeDecomp) : Nonempty t.W := t.isTree.connected.nonempty

/-- The width of a tree decomposition, as an extended natural number:
the maximum bag size minus one. -/
noncomputable def TreeDecomp.ewidth (t : TreeDecomp G) : ℕ∞ :=
  ⨆ w : t.W, #(t.𝓧 w) - 1

/-- `ℕ`-valued view of `TreeDecomp.ewidth`. -/
noncomputable def TreeDecomp.width (t : TreeDecomp G) : ℕ := t.ewidth.toNat

lemma TreeDecomp.ewidth_eq (t : TreeDecomp G) :
    t.ewidth = ⨆ w : t.W, (#(t.𝓧 w) - 1 : ℕ∞) := rfl

lemma TreeDecomp.le_ewidth {k : ℕ} (t : TreeDecomp G) :
    (∃ w : t.W, (k : ℕ∞) ≤ #(t.𝓧 w) - 1) → (k : ℕ∞) ≤ t.ewidth :=
  fun ⟨w, hw⟩ ↦ le_iSup_of_le w (by exact_mod_cast hw)

lemma TreeDecomp.ewidth_le {k : ℕ} (t : TreeDecomp G) :
    t.ewidth ≤ k ↔ ∀ w : t.W, #(t.𝓧 w) - 1 ≤ k := by
  rw [ewidth_eq, iSup_le_iff]
  enat_to_nat

/-- The cardinality of every bag is less than the ewidth + 1. -/
lemma TreeDecomp.card_bag_le (t : G.TreeDecomp) (w : t.W) :
    #(t.𝓧 w) ≤ t.ewidth + 1 := by
  have h : (#(t.𝓧 w) - 1 : ℕ∞) ≤ t.ewidth := le_iSup (fun w => (#(t.𝓧 w) - 1 : ℕ∞)) w
  calc (#(t.𝓧 w) : ℕ∞) ≤ #(t.𝓧 w) - 1 + 1 := le_tsub_add
    _ ≤ t.ewidth + 1 := by gcongr

/-- G has a tree decomposition with width at most n. -/
def hasTreeDecomp (G : SimpleGraph V) (n : ℕ∞) : Prop := ∃ t : G.TreeDecomp, t.ewidth ≤ n

@[mono]
lemma hasTreeDecomp.mono {n m : ℕ∞} (h : n ≤ m) : G.hasTreeDecomp n → G.hasTreeDecomp m := by
  intro ⟨t, ht⟩
  use t
  exact le_trans ht h

@[simp]
lemma TreeDecomp.coe_width {t : TreeDecomp G} (h : t.ewidth ≠ ⊤) :
    (t.width : ℕ∞) = t.ewidth := ENat.coe_toNat h

lemma TreeDecomp.card_bag_le_width (t : G.TreeDecomp) (hwidth : t.ewidth ≠ ⊤) (w : t.W) :
    #(t.𝓧 w) ≤ t.width + 1 := by
  have := t.card_bag_le w
  rw [← t.coe_width hwidth] at this
  exact_mod_cast this

lemma TreeDecomp.le_width {k : ℕ} (t : TreeDecomp G) (hwidth : t.ewidth ≠ ⊤) :
    k ≤ t.width ↔ (∃ w : t.W, k ≤ #(t.𝓧 w) - 1) := by
  suffices (k : ℕ∞) ≤ t.ewidth ↔ (∃ w : t.W, (k : ℕ∞) ≤ #(t.𝓧 w) - 1) by
    rw [← t.coe_width hwidth] at this; exact_mod_cast this
  refine ⟨fun h => ?_, fun ⟨w, hw⟩ => t.le_ewidth ⟨w, hw⟩⟩
  obtain ⟨w, hw⟩ := ENat.exists_eq_iSup_of_lt_top hwidth.lt_top
  exact ⟨w, hw.symm ▸ h⟩

lemma TreeDecomp.width_le {k : ℕ} (t : TreeDecomp G) (hwidth : t.ewidth ≠ ⊤) :
    t.width ≤ k ↔ ∀ w : t.W, #(t.𝓧 w) - 1 ≤ k := by
  rw [← Nat.cast_le (α := ℕ∞), t.coe_width hwidth, t.ewidth_le]

/-- On a finite vertex type, every tree decomposition has `width` at most `card V - 1`. -/
lemma TreeDecomp.ewidth_le_card [Fintype V] (t : TreeDecomp G) :
    t.ewidth ≤ card V - 1 :=
  iSup_le fun _ ↦ by
    exact_mod_cast Nat.sub_le_sub_right (Finset.card_le_univ _) 1

/-- On a finite vertex type, every tree decomposition has finite extended width. -/
lemma TreeDecomp.ewidth_ne_top_of_finite [Finite V] (t : TreeDecomp G) : t.ewidth ≠ ⊤ := by
  have := Fintype.ofFinite V
  exact (t.ewidth_le_card.trans_lt (ENat.coe_lt_top _)).ne

@[simp]
lemma TreeDecomp.coe_width_of_finite [Finite V] (t : TreeDecomp G) :
    (t.width : ℕ∞) = t.ewidth := t.coe_width t.ewidth_ne_top_of_finite

lemma TreeDecomp.width_le_iff_ewidth_le [Finite V] (t : TreeDecomp G) {k : ℕ} :
    t.width ≤ k ↔ t.ewidth ≤ k := by
  rw [← t.coe_width_of_finite]; enat_to_nat

/-- On a finite vertex type, every tree decomposition has width at most `card V - 1`. -/
lemma TreeDecomp.width_le_card [Fintype V] (t : TreeDecomp G) :
    t.width ≤ card V - 1 := by
  exact_mod_cast t.coe_width_of_finite ▸ t.ewidth_le_card

/-- Each bag of a tree decomposition has cardinality at most `width + 1` (finite-vertex form). -/
lemma TreeDecomp.card_bag_le_width_of_finite [Finite V] (t : G.TreeDecomp) (w : t.W) :
    #(t.𝓧 w) ≤ t.width + 1 := t.card_bag_le_width t.ewidth_ne_top_of_finite w

/-- Transport a tree decomposition along a graph isomorphism by mapping each bag. -/
noncomputable def TreeDecomp.iso (φ : G ≃g G') (t : G.TreeDecomp) : G'.TreeDecomp := { t with
  𝓧 w := (t.𝓧 w).map φ
  vertexCover v' := (t.vertexCover (φ.symm v')).imp fun _ ↦ Finset.mem_map_equiv.mpr
  edgeCover u' v' huv :=
    (t.edgeCover (φ.symm.map_rel_iff.mpr huv)).imp fun _ ⟨hu, hv⟩ ↦
      ⟨Finset.mem_map_equiv.mpr hu, Finset.mem_map_equiv.mpr hv⟩
  connectedBags v' := by
    have : {w : t.W | v' ∈ (t.𝓧 w).map φ} = {w | φ.symm v' ∈ t.𝓧 w} := by
      ext; exact Finset.mem_map_equiv
    exact this ▸ t.connectedBags (φ.symm v') }

@[simp]
lemma TreeDecomp.ewidth_iso (φ : G ≃g G') (t : G.TreeDecomp) :
    (t.iso φ).ewidth = t.ewidth := by
  simp only [TreeDecomp.ewidth_eq, TreeDecomp.iso, Finset.card_map]

lemma Iso.hasTreeDecomp {n : ℕ∞} (φ : G ≃g G') :
    G.hasTreeDecomp n ↔ G'.hasTreeDecomp n :=
  ⟨fun ⟨t, ht⟩ ↦ ⟨t.iso φ, TreeDecomp.ewidth_iso φ t ▸ ht⟩,
   fun ⟨t, ht⟩ ↦ ⟨t.iso φ.symm, TreeDecomp.ewidth_iso φ.symm t ▸ ht⟩⟩

/-- Pull back a tree decomposition along a graph embedding by taking the preimage of each bag. -/
noncomputable def TreeDecomp.comap (f : G ↪g G') (t : G'.TreeDecomp) : G.TreeDecomp where
  W := t.W
  𝓧 w := (t.𝓧 w).preimage f f.injective.injOn
  T := t.T
  isTree := t.isTree
  vertexCover v := (t.vertexCover (f v)).imp fun _ ↦ Finset.mem_preimage.mpr
  edgeCover u v huv :=
    (t.edgeCover (f.map_rel_iff.mpr huv)).imp fun _ ⟨hu, hv⟩ ↦
      ⟨Finset.mem_preimage.mpr hu, Finset.mem_preimage.mpr hv⟩
  connectedBags v := by
    have : {w : t.W | v ∈ (t.𝓧 w).preimage f f.injective.injOn} = {w | f v ∈ t.𝓧 w} := by
      ext; exact Finset.mem_preimage
    exact this ▸ t.connectedBags (f v)

lemma TreeDecomp.ewidth_comap_le (f : G ↪g G') (t : G'.TreeDecomp) :
    (t.comap f).ewidth ≤ t.ewidth := by
  refine iSup_mono fun w => ?_
  gcongr
  change ((t.𝓧 w).preimage f f.injective.injOn).card ≤ (t.𝓧 w).card
  exact Finset.card_le_card_of_injOn f
    (fun v hv => Finset.mem_preimage.mp hv) f.injective.injOn

lemma Embedding.hasTreeDecomp {n : ℕ∞} (f : G ↪g G') :
    G'.hasTreeDecomp n → G.hasTreeDecomp n :=
  fun ⟨t, ht⟩ => ⟨t.comap f, (TreeDecomp.ewidth_comap_le f t).trans ht⟩

/-- The tree decomposition of `⊥` indexed by `Option (Fin (Fintype.card V))` with a star graph
rooted at `none`: bags are `∅` at `none` and `{(Fintype.equivFin V).symm i}` at `some i`.
The vertex set `V` is encoded as `Fin (Fintype.card V) : Type 0` so the bag-indexing type fits
in `Type 0`. -/
noncomputable def botTreeDecomp [Fintype V] : (⊥ : SimpleGraph V).TreeDecomp where
  W := Option (Fin (Fintype.card V))
  𝓧 w := w.elim ∅ (fun i => {(Fintype.equivFin V).symm i})
  T := starGraph none
  isTree := isTree_starGraph _
  vertexCover v := ⟨some (Fintype.equivFin V v), by simp⟩
  edgeCover _ _ h := h.elim
  connectedBags v := by
    have : {w : Option (Fin (Fintype.card V)) |
        v ∈ w.elim ∅ (fun i => ({(Fintype.equivFin V).symm i} : Finset V))} =
        {some (Fintype.equivFin V v)} := by
      ext (_ | i) <;> simp [Equiv.eq_symm_apply, eq_comm]
    exact this ▸ Preconnected.of_subsingleton

lemma ewidth_botTreeDecomp [Fintype V] : (botTreeDecomp (V := V)).ewidth = 0 := by
  refine iSup_eq_bot.mpr ?_
  rintro (_ | w) <;> simp [botTreeDecomp]

/-- If G has a tree decomposition of width n, then the same decomposition applies for any
  subgraph. -/
@[mono]
lemma TreeDecomp.mono {G' : SimpleGraph V} {n : ℕ∞} (h : G' ≤ G) (hG : G.hasTreeDecomp n) :
    G'.hasTreeDecomp n := by
  obtain ⟨t, ht⟩ := hG
  exact ⟨{ t with edgeCover := fun _ _ huv ↦ t.edgeCover (h huv)}, ht⟩

end TreeDecomp

section TreeWidth

/-- The tree width of a simple graph, as an extended natural number:
the infimum of widths over all tree decompositions, valued in `ℕ∞`. -/
noncomputable def etreeWidth (G : SimpleGraph V) : ℕ∞ :=
  ⨅ t : TreeDecomp G, t.ewidth

/-- `ℕ`-valued view of `etreeWidth`, with junk value `0` when the treewidth is `⊤`. -/
noncomputable def treeWidth (G : SimpleGraph V) : ℕ := G.etreeWidth.toNat

lemma treeDecomp_imp_etreeWidth_le (treeDecomp : G.TreeDecomp) :
    G.etreeWidth ≤ treeDecomp.ewidth :=
  iInf_le _ treeDecomp

@[simp]
lemma coe_treeWidth (h : G.etreeWidth ≠ ⊤) : G.treeWidth = G.etreeWidth := ENat.coe_toNat h

/-- G has extended treewidth ≤ k iff G has a tree decomposition of width k, where k is finite. -/
@[simp]
lemma etreeWidth_le_iff_hasTreeDecomp (k : ℕ) :
    G.etreeWidth ≤ k ↔ G.hasTreeDecomp k := by
  refine ⟨fun h ↦ ?_, fun h ↦ (treeDecomp_imp_etreeWidth_le h.choose).trans h.choose_spec⟩
  by_contra hc
  rw [hasTreeDecomp, not_exists] at hc
  have : (k + 1 : ℕ∞) ≤ G.etreeWidth := by
    exact le_iInf fun t ↦ (ENat.add_one_le_iff (ENat.coe_ne_top k)).mpr (not_le.mp (hc t))
  exact absurd (this.trans h) (by enat_to_nat; omega)

@[simp]
lemma le_etreeWidth_iff {k : ℕ∞} : k ≤ G.etreeWidth ↔ ∀ t : G.TreeDecomp, k ≤ t.ewidth :=
  le_iInf_iff

/-- The tree decomposition obtained by putting all vertices in one bag. -/
def trivialTreeDecomp [Fintype V] (G : SimpleGraph V) : G.TreeDecomp where
  W := Unit
  𝓧 := fun _ ↦ univ
  T := ⊥
  isTree := by exact IsTree.of_subsingleton
  vertexCover := by simp
  edgeCover := by simp
  connectedBags := by aesop_graph

lemma ewidth_trivialTreeDecomp [Fintype V] :
    (G.trivialTreeDecomp).ewidth = (card V - 1 : ℕ) := by
  simp [TreeDecomp.ewidth_eq, trivialTreeDecomp]

/-- The treewidth of a finite graph is at most `card V - 1`. -/
lemma etreeWidth_le_card [Fintype V] : G.etreeWidth ≤ card V - 1 :=
  (treeDecomp_imp_etreeWidth_le G.trivialTreeDecomp).trans ewidth_trivialTreeDecomp.le

@[gcongr]
lemma etreeWidth_mono {G' : SimpleGraph V} (h : G' ≤ G) : G'.etreeWidth ≤ G.etreeWidth := by
  cases hw : G.etreeWidth
  · simp
  · expose_names
    rw [etreeWidth_le_iff_hasTreeDecomp]
    exact TreeDecomp.mono h ((etreeWidth_le_iff_hasTreeDecomp a).mp hw.le)

lemma etreeWidth_mono_of_embedding (f : G ↪g G') : G.etreeWidth ≤ G'.etreeWidth := by
  cases hw : G'.etreeWidth
  · simp
  · expose_names
    rw [etreeWidth_le_iff_hasTreeDecomp]
    exact f.hasTreeDecomp ((etreeWidth_le_iff_hasTreeDecomp a).mp hw.le)

/-- On a finite vertex type, the extended treewidth is finite. -/
lemma etreeWidth_ne_top_of_finite [Finite V] : G.etreeWidth ≠ ⊤ := by
  have := Fintype.ofFinite V
  exact (etreeWidth_le_card.trans_lt (ENat.coe_lt_top _)).ne

@[simp]
lemma coe_treeWidth_of_finite [Finite V] : (G.treeWidth : ℕ∞) = G.etreeWidth :=
  coe_treeWidth etreeWidth_ne_top_of_finite

@[simp]
lemma treeWidth_le_iff_etreeWidth_le [Finite V] {k : ℕ} :
    G.treeWidth ≤ k ↔ G.etreeWidth ≤ k := by
  rw [← coe_treeWidth_of_finite]; enat_to_nat

/-- G has treewidth at most `k` (as a natural number) iff it has a tree decomposition of width
at most `k`. -/
theorem treeWidth_le_iff_hasTreeDecomp [Finite V] (k : ℕ) :
    G.treeWidth ≤ k ↔ G.hasTreeDecomp k :=
  treeWidth_le_iff_etreeWidth_le.trans (etreeWidth_le_iff_hasTreeDecomp k)

@[simp]
lemma le_treeWidth_iff [Finite V] {k : ℕ} :
    k ≤ G.treeWidth ↔ ∀ t : G.TreeDecomp, k ≤ t.width := by
  simp [← Nat.cast_le (α := ℕ∞)]

/-- The treewidth of a finite graph is at most `card V - 1`. -/
theorem treeWidth_le_card [Fintype V] : G.treeWidth ≤ card V - 1 :=
  treeWidth_le_iff_etreeWidth_le.mpr etreeWidth_le_card

@[gcongr]
lemma treeWidth_mono {G' : SimpleGraph V} [Finite V] (h : G' ≤ G) : G'.treeWidth ≤ G.treeWidth := by
  simpa using etreeWidth_mono h

lemma treeWidth_mono_of_embedding [Finite V] [Finite V']
    (f : G ↪g G') : G.treeWidth ≤ G'.treeWidth := by
  simpa using etreeWidth_mono_of_embedding f

/-- Tree-width is monotone under graph containment: if `B` contains a copy of `A`, then `A`'s
extended tree-width is at most `B`'s. -/
theorem IsContained.etreeWidth_le {A : SimpleGraph V} {B : SimpleGraph V'} (h : A ⊑ B) :
    A.etreeWidth ≤ B.etreeWidth := by
  obtain ⟨f⟩ := h
  calc A.etreeWidth
      ≤ f.toSubgraph.coe.etreeWidth :=
        etreeWidth_mono_of_embedding f.isoToSubgraph.toEmbedding
    _ ≤ f.toSubgraph.spanningCoe.etreeWidth :=
        etreeWidth_mono_of_embedding f.toSubgraph.coeEmbeddingSpanningCoe
    _ ≤ B.etreeWidth := etreeWidth_mono f.toSubgraph.spanningCoe_le

/-- ℕ-valued version of `IsContained.etreeWidth_le`. -/
theorem IsContained.treeWidth_le {A : SimpleGraph V} {B : SimpleGraph V'}
    [Finite V] [Finite V'] (h : A ⊑ B) : A.treeWidth ≤ B.treeWidth := by
  simpa using h.etreeWidth_le

lemma treeWidth_bot [Finite V] : (⊥ : SimpleGraph V).treeWidth = 0 := by
  have := Fintype.ofFinite V
  have : (⊥ : SimpleGraph V).etreeWidth = 0 :=
    le_antisymm ((treeDecomp_imp_etreeWidth_le botTreeDecomp).trans ewidth_botTreeDecomp.le)
      zero_le
  simp [treeWidth, this]

/-- The treewidth of a graph is positive iff it has an edge. -/
theorem treeWidth_ne_zero_iff_ne_bot [Finite V] : 0 < G.treeWidth ↔ G ≠ ⊥ := by
  classical
  have := Fintype.ofFinite V
  rw [← Order.one_le_iff_pos, le_treeWidth_iff]
  refine ⟨?_, ?_⟩
  · contrapose!
    intro h
    have htw := h ▸ treeWidth_bot
    obtain ⟨t, ht⟩ := (G.treeWidth_le_iff_hasTreeDecomp 0).mp htw.le
    rw [← t.width_le_iff_ewidth_le] at ht
    exact ⟨t, by omega⟩
  · rw [SimpleGraph.ne_bot_iff_exists_adj]
    rintro ⟨u, v, huv⟩ t
    obtain ⟨w, hu, hv⟩ := t.edgeCover huv
    have := Finset.one_lt_card.mpr ⟨u, hu, v, hv, huv.ne⟩
    exact (t.le_width t.ewidth_ne_top_of_finite).mpr ⟨w, by omega⟩

end TreeWidth

section Clique

/-- A tree decomposition is trivial if some bag contains every element. -/
def TreeDecomp.IsTrivial (t : G.TreeDecomp) : Prop := ∃ w : t.W, ∀ v : V, v ∈ t.𝓧 w

/-- A tree decomposition is trivial iff every pair of distinct vertices is contained in some bag. -/
lemma TreeDecomp.isTrivial_iff [Nonempty V] [Finite V] (t : G.TreeDecomp) : t.IsTrivial ↔
    ∀ u v : V, u ≠ v → ∃ w : t.W, u ∈ t.𝓧 w ∧ v ∈ t.𝓧 w := by
  letI := Fintype.ofFinite V
  simp only [IsTrivial]
  refine ⟨fun ⟨w, hw⟩ u v _ => ⟨w, hw u, hw v⟩, fun h => ?_⟩
  let f (x : V) := {w | x ∈ t.𝓧 w}
  have h_conn : ∀ i ∈ (univ : Finset V), (t.T.induce (f i)).Connected := fun v _ => by
    rw [connected_iff]
    obtain ⟨w, hw⟩ := t.vertexCover v
    exact ⟨t.connectedBags v, ⟨⟨w, hw⟩⟩⟩
  have h_pair : ∀ i ∈ (univ : Finset V), ∀ j ∈ (univ : Finset V), (f i ∩ f j).Nonempty := by
    intro i _ j _
    by_cases hij : i = j
    · subst hij; exact (t.vertexCover i).imp fun _ hw => ⟨hw, hw⟩
    · exact h i j hij
  obtain ⟨w, hw⟩ := t.isTree.inter_nonempty_of_pairwise Finset.univ_nonempty h_conn h_pair
  use w
  simp only [mem_univ, Set.iInter_true, Set.mem_iInter, Set.mem_setOf_eq, f] at hw
  exact hw

lemma TreeDecomp.not_isTrivial_iff [Nonempty V] [Finite V] (t : G.TreeDecomp) : ¬t.IsTrivial ↔
    ∃ u v : V, u ≠ v ∧ ∀ w : t.W, u ∉ t.𝓧 w ∨ v ∉ t.𝓧 w := by
  simp [isTrivial_iff, imp_iff_not_or]

lemma TreeDecomp.isTrivial_width [Nonempty V] [Fintype V] (t : G.TreeDecomp) :
    t.IsTrivial ↔ t.width = card V - 1 := by
  have hwidth := t.ewidth_ne_top_of_finite
  refine ⟨fun ⟨w, hw⟩ => le_antisymm t.width_le_card ?_, fun h => ?_⟩
  · rw [t.le_width hwidth]
    exact ⟨w, by rw [eq_univ_iff_forall.mpr hw, card_univ]⟩
  · by_cases hV : card V ≤ 1
    · obtain ⟨v⟩ := ‹Nonempty V›
      obtain ⟨w, hw⟩ := t.vertexCover v
      rw [← Finset.card_univ, card_le_one_iff] at hV
      refine ⟨w, fun v' => ?_⟩
      have hvv : v' = v := hV (mem_univ _) (mem_univ _)
      exact hvv ▸ hw
    · obtain ⟨w, hw⟩ := (t.le_width hwidth).mp h.ge
      have hle : #(t.𝓧 w) ≤ card V := card_le_univ _
      exact ⟨w, fun v => ((t.𝓧 w).card_eq_iff_eq_univ.mp (by omega)).symm ▸ mem_univ v⟩

lemma TreeDecomp.width_lt_iff_not_isTrivial [Nonempty V] [Fintype V] (t : G.TreeDecomp) :
    t.width < card V - 1 ↔ ¬t.IsTrivial := by
  rw [t.isTrivial_width, lt_iff_le_and_ne, and_iff_right t.width_le_card]

theorem treewidth_top [Fintype V] : (⊤ : SimpleGraph V).treeWidth = card V - 1 := by
  refine le_antisymm treeWidth_le_card ?_
  rcases isEmpty_or_nonempty V with hV | hV
  · simp
  simp only [le_treeWidth_iff]
  intro t
  exact (t.isTrivial_width.mp <|
    t.isTrivial_iff.mpr fun u v huv => t.edgeCover ((top_adj u v).mpr huv)).ge

@[simp]
lemma etreewidth_top [Fintype V] : (⊤ : SimpleGraph V).etreeWidth = (card V - 1 : ℕ) := by
  rw [← coe_treeWidth_of_finite, treewidth_top]

theorem isClique_card_le_etreeWidth (s : Finset V) :
    G.IsClique s → s.card - 1 ≤ G.etreeWidth := by
  rw [isClique_iff_induce_eq]
  intro h
  calc (s.card - 1 : ℕ∞)
      = (induce (↑s) G).etreeWidth := by simp [h]
    _ ≤ G.etreeWidth := etreeWidth_mono_of_embedding (SimpleGraph.Embedding.induce (↑s : Set V))

theorem isClique_card_le_treeWidth [Finite V] (s : Finset V) (h : G.IsClique s) :
    s.card - 1 ≤ G.treeWidth := by
  have := isClique_card_le_etreeWidth s h
  rw [← coe_treeWidth_of_finite] at this
  exact_mod_cast this

theorem cliqueNum_le_treeWidth [Finite V] : G.cliqueNum - 1 ≤ G.treeWidth := by
  obtain ⟨s, hs⟩ := G.maximumClique_exists
  have := maximumClique_card_eq_cliqueNum s hs
  exact this ▸ isClique_card_le_treeWidth s hs.isClique

end Clique

section Adhesion
namespace TreeDecomp

variable [DecidableEq V] (t : G.TreeDecomp)

/-- Given a tree decomposition (𝓧, T) and some edge `e`, `t.adhesion e` is the intersection of bags
  between endpoints of `e`. -/
@[nolint unusedArguments]
def adhesion {x y : t.W} (_ : t.T.Adj x y)
    : Finset V := (t.𝓧 x) ∩ (t.𝓧 y)

@[simp]
lemma mem_adhesion {x y : t.W} (e : t.T.Adj x y)
    {v : V} : v ∈ t.adhesion e ↔ v ∈ t.𝓧 x ∧ v ∈ t.𝓧 y := by
  simp [adhesion]

@[simp]
lemma not_mem_adhesion {x y : t.W} (e : t.T.Adj x y)
    {v : V} : v ∉ t.adhesion e ↔ v ∉ t.𝓧 x ∨ v ∉ t.𝓧 y := by
  simp only [mem_adhesion, not_and_or]

/-- The "induced separation" on V of one side of a cut tree edge: the union of bags on that
  side, minus the adhesion. Parametrized by a side vertex `z : t.W`. -/
def inducedSeparation {x y : t.W}
    (e : t.T.Adj x y) (z : t.W) : Set V :=
  (⋃ w ∈ (t.T.subtreeOfCut t.isTree {s(x, y)} z).supp, (t.𝓧 w : Set V)) \ t.adhesion e

@[simp]
lemma mem_inducedSeparation {x y : t.W} {v : V} (e : t.T.Adj x y) (z : t.W) :
    v ∈ t.inducedSeparation e z ↔ v ∉ t.adhesion e ∧
    ∃ w ∈ (t.T.subtreeOfCut t.isTree {s(x, y)} z).supp, v ∈ t.𝓧 w := by
  rw [inducedSeparation, Set.mem_diff, and_comm]
  simp only [Set.mem_iUnion, Finset.mem_coe, exists_prop]

theorem disjoint_inducedSeparation {x y : t.W}
    (e : t.T.Adj x y) :
    Disjoint (t.inducedSeparation e x) (t.inducedSeparation e y) := by
  classical
  rw [Set.disjoint_left]
  intro v hvx hvy
  obtain ⟨hv_not_adh, w₁, hw₁_supp, hv₁⟩ := (t.mem_inducedSeparation e x).mp hvx
  obtain ⟨_, w₂, hw₂_supp, hv₂⟩ := (t.mem_inducedSeparation e y).mp hvy
  obtain ⟨q, hq⟩ := preconnected_induce_iff_forall_exists_walk.mp (t.connectedBags v) hv₁ hv₂
  let p : t.T.Path w₁ w₂ := q.toPath
  have hxy : s(x, y) ∈ p.val.edges :=
    t.T.path_mem_cutEdge_of_subtreeOfCut_ne t.isTree p
      (fun h => t.T.disjoint_subtreeOfCut t.isTree e
        ((hw₁_supp : _ = _).symm.trans (h.trans hw₂_supp)))
  have hp_sub := Walk.support_toPath_subset q
  exact hv_not_adh ((t.mem_adhesion e).mpr
    ⟨hq x (hp_sub (p.val.fst_mem_support_of_mem_edges hxy)),
     hq y (hp_sub (p.val.snd_mem_support_of_mem_edges hxy))⟩)

/-- If there is no bag that contains u and v, then there is a proper adhesion set satisfying
  1. Its size is ≤ t.width
  2. u and v are in different sides of the induced separation.
-/
theorem exists_proper_adhesion [Nonempty V] [Finite V] (u v : V) :
    ¬(∃ w : t.W, u ∈ t.𝓧 w ∧ v ∈ t.𝓧 w) →
    (∃ x y : t.W, ∃ h : t.T.Adj x y, #(t.adhesion h) ≤ t.width ∧
    u ∈ t.inducedSeparation h x ∧ v ∈ t.inducedSeparation h y) := by
    intro h_sep
    push Not at h_sep
    obtain ⟨w₀, hw₀⟩ := t.vertexCover u
    obtain ⟨w₁, hw₁⟩ := t.vertexCover v
    obtain ⟨p, hp_path, _⟩ := t.isTree.existsUnique_path w₀ w₁
    obtain ⟨d, hd_in, hfst, hsnd⟩ :=
      p.exists_boundary_dart {w | u ∈ t.𝓧 w} hw₀ (h_sep w₁ · hw₁)
    refine ⟨d.fst, d.snd, d.adj, ?_⟩
    constructor
    · simp only [Set.mem_setOf_eq] at hfst hsnd
      have huv : t.𝓧 d.fst ≠ t.𝓧 d.snd := fun heq => hsnd (heq ▸ hfst)
      rw [adhesion]
      have hbu := t.card_bag_le_width_of_finite d.fst
      have hbv := t.card_bag_le_width_of_finite d.snd
      have hcard_eq := Finset.card_union_add_card_inter (t.𝓧 d.fst) (t.𝓧 d.snd)
      have hcard_lt : #(t.𝓧 d.fst ∩ t.𝓧 d.snd) < #(t.𝓧 d.fst ∪ t.𝓧 d.snd) :=
        Finset.card_lt_card (inf_lt_sup.mpr huv)
      omega
    · simp only [mem_inducedSeparation, not_mem_adhesion]
      refine ⟨⟨Or.inr hsnd, d.fst, rfl, hfst⟩, Or.inl (h_sep d.fst hfst), w₁, ?_, hw₁⟩
      exact (t.T.subtreeOfCut_endpoints_of_dart_mem_path t.isTree ⟨p, hp_path⟩ hd_in).2

/-- If u, v are in the induced separation from an edge, any walk between u, v contains some node in
  the adhesion set. -/
lemma mem_adhesion_of_inducedSeparation_walk {u v : V} {x y : t.W} (e : t.T.Adj x y)
    (hu : u ∈ t.inducedSeparation e x) (hv : v ∈ t.inducedSeparation e y) :
    ∀ walk : G.Walk u v, walk.toSubgraph.verts ∩ t.adhesion e ≠ ∅ := by
  intro walk h
  have hv_notin : v ∉ t.inducedSeparation e x :=
    Set.disjoint_right.mp (t.disjoint_inducedSeparation e) hv
  obtain ⟨d, hd_in, hd_fst_in, hd_snd_notin⟩ :=
    walk.exists_boundary_dart (t.inducedSeparation e x) hu hv_notin
  have nmem : ∀ z, z ∈ walk.toSubgraph.verts → z ∉ ↑(t.adhesion e) :=
    fun z hz hadh => Set.notMem_empty z (h ▸ ⟨hz, hadh⟩)
  have h_fst_walk :=
    walk.mem_verts_toSubgraph.mpr (walk.dart_fst_mem_support_of_mem_darts hd_in)
  have h_snd_walk :=
    walk.mem_verts_toSubgraph.mpr (walk.dart_snd_mem_support_of_mem_darts hd_in)
  obtain ⟨w₀, h_fst_w₀, h_snd_w₀⟩ := t.edgeCover d.adj
  rcases t.T.subtreeOfCut_eq_or_eq t.isTree e w₀ with hw₀_x | hw₀_y
  · exact hd_snd_notin ⟨Set.mem_iUnion₂.mpr ⟨w₀, hw₀_x, h_snd_w₀⟩, nmem _ h_snd_walk⟩
  · exact Set.disjoint_left.mp (t.disjoint_inducedSeparation e) hd_fst_in
      ⟨Set.mem_iUnion₂.mpr ⟨w₀, hw₀_y, h_fst_w₀⟩, nmem _ h_fst_walk⟩

/-- If u and v are on different sides of the induced separation from an edge, then its adhesion
  set separates u and v on the graph. -/
theorem adhesion_imp_separator [Nonempty V] [Finite V] {u v : V} {x y : t.W} (e : t.T.Adj x y)
    (hu : u ∈ t.inducedSeparation e x) (hv : v ∈ t.inducedSeparation e y) :
    G.IsSeparator (t.adhesion e) u v := by
  rw [isSeparator_iff_walk_cover]
  have mem_adh := t.mem_adhesion_of_inducedSeparation_walk e hu hv
  simp only [mem_inducedSeparation] at hu hv
  refine ⟨hu.left, hv.left, fun walk => ?_⟩
  obtain ⟨z, hzw, hza⟩ := Set.inter_nonempty.mp (Set.nonempty_iff_ne_empty.mpr (mem_adh walk))
  exact ⟨z, hza, hzw⟩

end TreeDecomp
end Adhesion

section Acyclic

/-- Every acyclic graph on a nonempty vertex type is contained in a tree, obtained as a
maximal acyclic extension. -/
theorem IsAcyclic.exists_isTree_ge [Nonempty V] (hG : G.IsAcyclic) :
    ∃ T : SimpleGraph V, G ≤ T ∧ T.IsTree := by
  obtain ⟨T, hGT, hT⟩ :=
    (⊤ : SimpleGraph V).exists_maximal_isAcyclic_of_le_isAcyclic le_top hG
  exact ⟨T, hGT, (connected_top.maximal_le_isAcyclic_iff_isTree le_top).mp hT⟩

/-- A cycle graph with ≥ 3 vertices has treewidth > 1. -/
theorem cycleGraph_le_treewidth (n : ℕ) : 1 < (cycleGraph (n+3)).treeWidth := by
  by_contra! h
  obtain ⟨t, ht⟩ := (treeWidth_le_iff_hasTreeDecomp _).mp h
  rw [← t.width_le_iff_ewidth_le] at ht
  obtain ⟨u, v, huv, h_not_bag⟩ := t.not_isTrivial_iff.mp
    (t.width_lt_iff_not_isTrivial.mp (by simp; omega))
  have h_no_share : ¬∃ w, u ∈ t.𝓧 w ∧ v ∈ t.𝓧 w :=
    fun ⟨w, hu, hv⟩ => (h_not_bag w).elim (· hu) (· hv)
  by_cases hsize : n + 3 = 3
  · obtain rfl : n = 0 := by omega
    exact h_no_share (t.edgeCover (cycleGraph_three_eq_top.symm ▸ (top_adj u v).mpr huv))
  · have sep_card := two_le_card_separator_of_disjoint_walks
      (cycleGraph.disjoint_ccwPath_cwPath u v huv)
    obtain ⟨x, y, adh, adh_card, u_adh, v_adh⟩ := t.exists_proper_adhesion u v h_no_share
    have := sep_card _ (t.adhesion_imp_separator adh u_adh v_adh)
    grw [ht] at adh_card
    lia

/-- Every tree has treewidth at most 1. Transports to `Fin (Fintype.card V)` via
[[SimpleGraph.overFinIso]] so the bag-indexing type fits the `Type 0` slot of `TreeDecomp.W`,
then builds the incidence-graph (Levi-graph) tree decomposition: vertex-nodes carry singleton
bags, edge-nodes carry their two endpoints, and `T` is the bipartite incidence graph. -/
theorem isTree_treewidth [Nonempty V] [Finite V] (ht : G.IsTree) : G.treeWidth ≤ 1 := by
  classical
  haveI : Fintype V := Fintype.ofFinite V
  let iso : G ≃g G.overFin rfl := G.overFinIso rfl
  -- Chosen root vertex in the `Fin n` encoding; used to anchor the connectedness argument.
  let r : Fin (Fintype.card V) := iso (Classical.arbitrary V)
  rw [treeWidth_le_iff_hasTreeDecomp, iso.hasTreeDecomp]
  set G' := G.overFin rfl
  have ht' : G'.IsTree := iso.isTree_iff.mp ht
  set T : SimpleGraph (Fin (Fintype.card V) ⊕ G'.edgeSet) :=
    SimpleGraph.fromRel fun a b => match a, b with
      | .inl v, .inr e => v ∈ e.val
      | _, _ => False
  -- `v ∈ e.val` is exactly the bipartite incidence relation underlying `T`.
  have hT_mk : ∀ {v : Fin (Fintype.card V)} {e : G'.edgeSet},
      v ∈ e.val → T.Adj (.inl v) (.inr e) := fun hv =>
    (fromRel_adj _ _ _).mpr ⟨Sum.inl_ne_inr, .inl hv⟩
  refine ⟨{
    W := Fin (Fintype.card V) ⊕ G'.edgeSet
    𝓧 := Sum.elim (fun v => {v}) (fun e => e.val.toFinset)
    T := T
    isTree := ?_
    vertexCover := ?_
    edgeCover := ?_
    connectedBags := ?_ }, ?_⟩
  · -- T (Levi graph of a tree) is itself a tree.
    -- Lift each G'-walk to a T-walk through the corresponding edge-nodes.
    refine isTree_iff_connected_and_card.mpr ⟨?_, ?_⟩
    · -- Connected: `Nonempty W` via the root `r`; `Preconnected` by routing every vertex
      -- to `.inl r` using `liftWalk` (plus one bridge edge for edge-nodes).
      have liftAdj : ∀ {u v : Fin (Fintype.card V)} (h : G'.Adj u v),
          T.Adj (.inl u) (.inr ⟨s(u, v), h⟩) ∧ T.Adj (.inr ⟨s(u, v), h⟩) (.inl v) := fun _ =>
        ⟨hT_mk (by simp), (hT_mk (by simp)).symm⟩
      have liftWalk : ∀ {u v : Fin (Fintype.card V)}, G'.Walk u v →
          T.Walk (.inl u) (.inl v) := by
        intro u v p
        induction p with
        | nil => exact .nil
        | @cons u w v h q ih => exact .cons (liftAdj h).1 (.cons (liftAdj h).2 ih)
      haveI : Nonempty (Fin (Fintype.card V) ⊕ G'.edgeSet) := ⟨.inl r⟩
      refine ⟨fun a b => ?_⟩
      suffices h : ∀ w, T.Reachable w (.inl r) from (h a).trans (h b).symm
      rintro (x | ⟨e, he⟩)
      · exact ⟨liftWalk (ht'.connected.preconnected x r).some⟩
      · exact ⟨.cons (hT_mk (Sym2.out_fst_mem e)).symm
          (liftWalk (ht'.connected.preconnected e.out.1 r).some)⟩
    · -- Cardinality: `|T.edgeSet| + 1 = |W|`.
      -- `|W| = n + |G'.edgeSet|`, and each G'-edge yields 2 incident T-edges (one per
      -- endpoint), so `|T.edgeSet| = 2|G'.edgeSet|`. Using `G'` tree (`|G'.edgeSet| = n - 1`):
      -- `|T.edgeSet| + 1 = 2(n-1) + 1 = 2n - 1 = n + (n-1) = |W|`.
      have hG'card : Nat.card G'.edgeSet + 1 = Fintype.card V := by
        simpa [Nat.card_eq_fintype_card] using (isTree_iff_connected_and_card.mp ht').2
      -- Bijection `T.edgeSet ≃ Σ e : G'.edgeSet, ↥e.val.toFinset` — index by edge then
      -- pick one of its two endpoints (as elements of `e.val.toFinset`).
      let toEdge : (Σ e : G'.edgeSet, ↥e.val.toFinset) → T.edgeSet :=
        fun ⟨e, v, hv⟩ => ⟨s((Sum.inl v : Fin _ ⊕ G'.edgeSet), .inr e),
          T.mem_edgeSet.mpr (hT_mk (Sym2.mem_toFinset.mp hv))⟩
      have toEdge_inj : Function.Injective toEdge := by
        rintro ⟨e₁, v₁, _⟩ ⟨e₂, v₂, _⟩ heq
        rcases Sym2.eq_iff.mp (Subtype.ext_iff.mp heq) with ⟨ha, hb⟩ | ⟨ha, _⟩
        · grind only
        · exact absurd ha Sum.inl_ne_inr
      have toEdge_surj : Function.Surjective toEdge := by
        rintro ⟨s, hs⟩
        refine s.ind (fun a b hs => ?_) hs
        rcases (fromRel_adj _ _ _).mp ((T.mem_edgeSet).mp hs) with ⟨_, hr | hr⟩
        · rcases a with x | _ <;> rcases b with _ | e <;> first | exact hr.elim |
            exact ⟨⟨e, x, Sym2.mem_toFinset.mpr hr⟩, rfl⟩
        · rcases a with _ | e <;> rcases b with y | _ <;> first | exact hr.elim |
            exact ⟨⟨e, y, Sym2.mem_toFinset.mpr hr⟩, Subtype.ext Sym2.eq_swap⟩
      let edgeEquiv : T.edgeSet ≃ Σ e : G'.edgeSet, ↥e.val.toFinset :=
        (Equiv.ofBijective toEdge ⟨toEdge_inj, toEdge_surj⟩).symm
      have hT_eq : Nat.card T.edgeSet = 2 * Nat.card G'.edgeSet := by
        rw [Nat.card_congr edgeEquiv, Nat.card_sigma]
        have hfib : ∀ e : G'.edgeSet, Nat.card ↥e.val.toFinset = 2 := fun e =>
          (Nat.card_eq_finsetCard _).trans
            (Sym2.card_toFinset_of_not_isDiag _ (G'.not_isDiag_of_mem_edgeSet e.2))
        rw [Finset.sum_const_nat (fun e _ => hfib e), Finset.card_univ,
            Nat.card_eq_fintype_card, mul_comm]
      rw [hT_eq, Nat.card_sum, Nat.card_eq_fintype_card (α := Fin _), Fintype.card_fin]
      omega
  · -- vertexCover: vertex v lives in its own vertex-node bag.
    exact fun v => ⟨.inl v, by simp⟩
  · -- edgeCover: edge (u,v) lives in the edge-node bag for s(u,v).
    intro u v huv
    refine ⟨.inr ⟨s(u, v), huv⟩, ?_, ?_⟩ <;> simp [Sym2.mem_toFinset]
  · -- connectedBags: bags containing v form a star at `.inl v` ⇒ preconnected.
    -- Every bag-set node is either the centre `.inl x` itself or T-adjacent to it.
    intro x
    set S : Set (Fin (Fintype.card V) ⊕ G'.edgeSet) :=
      {w | x ∈ Sum.elim (fun v => ({v} : Finset _)) (fun e => e.val.toFinset) w}
    suffices h : ∀ w : ↥S, (_ : SimpleGraph _).Reachable w ⟨.inl x, by simp [S]⟩ from
      fun u v => (h u).trans (h v).symm
    rintro ⟨y | ⟨e, he⟩, hw⟩
    · obtain rfl : x = y := by simpa [S] using hw
      rfl
    · have hxe : x ∈ e := by simpa [S] using hw
      exact (induce_adj.mpr (hT_mk hxe).symm).reachable
  · -- width: vertex-bags have card 1, edge-bags have card 2 (non-diagonal).
    rw [TreeDecomp.ewidth_le]
    rintro (v | ⟨e, he⟩)
    · simp
    · simp [Sym2.card_toFinset_of_not_isDiag _ (G'.not_isDiag_of_mem_edgeSet he)]

/-- A graph is acyclic iff it has treewidth ≤ 1. -/
theorem isAcyclic_iff_treewidth_le [Nonempty V] [Finite V] :
    G.IsAcyclic ↔ G.treeWidth ≤ 1 := by
  constructor
  · intro h
    obtain ⟨T, hGT, hT⟩ := h.exists_isTree_ge
    exact (treeWidth_mono hGT).trans (isTree_treewidth hT)
  · rw [IsAcyclic]
    contrapose!
    rintro ⟨v, c, hc⟩
    have len := hc.three_le_length
    obtain ⟨n, hn⟩ : ∃ n, c.length = n + 3 := ⟨c.length - 3, by omega⟩
    have contained := (cycleGraph_isContained_iff len).mpr ⟨v, c, hc, rfl⟩
    exact (cycleGraph_le_treewidth n).trans_le (hn ▸ contained.treeWidth_le)

end Acyclic

end SimpleGraph
