/-
Copyright (c) 2026 Justin Lai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justin Lai
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Combinatorics.SimpleGraph.Star
public import Mathlib.Data.Int.Cast.Basic

/-!
# Tree Decompositions and Tree Width

This file defines tree decompositions on simple graphs and the treewidth parameter.

## Main definitions

* `SimpleGraph.TreeDecomp` is a tree decomposition of a simple graph.
* `TreeDecomp.ewidth` is the extended width of the tree decomposition. `TreeDecomp.width` is the
  ℕ-valued version.
* `SimpleGraph.hasTreeDecomp n` is a predicate that a simple graph has a tree decomposition of width
  at most n.
* `SimpleGraph.etreeWidth` is the extended tree width of a simple graph. `SimpleGraph.treeWidth` is
  the ℕ-valued version.

## Conventions

The user-facing API uses `treeWidth : SimpleGraph V → ℕ`. The extended version
`etreeWidth : SimpleGraph V → ℕ∞` is mostly an implementation detail that handles the corner case
of graphs without finite treewidth (returning `⊤`). For `[Finite V]`, the two are interchangeable
via `treeWidth_le_iff_etreeWidth_le` (a `simp` lemma) and `treeWidth_le_iff_hasTreeDecomp`. State
theorems in `treeWidth` form unless infinite-vertex graphs are genuinely in scope.

## Main statements

* `treeWidth_le_card` shows that a finite graph must have finite treewidth.
* `etreeWidth_ne_zero_iff_ne_bot` shows that a graph has nonzero treewidth iff it is nonempty.
* `treewidth_top` shows that the complete graph on a finite vertex type has treewidth `card V - 1`.

## References

* [R. Diestel **Graph Theory**
  https://doi.org/10.1007/978-3-662-70107-2][diestel2025]

## TODO

- Refactor (add a simp lemma for treewidth ≥ k)
- Fix proper adhesion lemma
- Prove adhesion set is a separator (with new notation)

* Prove `G.IsAcyclic ↔ G.treewidth ≤ 1`.

## Tags
tree decomposition, treewidth

-/

@[expose] public section

open Finset Fintype

namespace SimpleGraph

universe u v
variable {V V' : Type u}
variable {G : SimpleGraph V} {G' : SimpleGraph V'}

/-! ## Tree decompositions -/

section TreeDecomp

/-- A tree decomposition of a simple graph `G` is a tree `T` indexed by a type
`W`, together with a bag `𝓧 w : Finset V` assigned to each `w : W`, such that
every edge of `G` lies in some bag and the bags containing any fixed vertex form
a connected subgraph of `T`. -/
structure TreeDecomp (G : SimpleGraph V) where
  /-- The type of bags in the tree. -/
  W : Type u
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

/-- The width of a tree decomposition, as an extended natural number:
the maximum bag size minus one. -/
noncomputable def TreeDecomp.ewidth (t : TreeDecomp G) : ℕ∞ :=
  ⨆ w : t.W, #(t.𝓧 w) - 1

/-- `ℕ`-valued view of `TreeDecomp.ewidth`, with junk value `0` when the width is `⊤`. -/
noncomputable def TreeDecomp.width (t : TreeDecomp G) : ℕ := t.ewidth.toNat

lemma TreeDecomp.ewidth_eq (t : TreeDecomp G) :
    t.ewidth = ⨆ w : t.W, (#(t.𝓧 w) - 1 : ℕ∞) := rfl

lemma TreeDecomp.ewidth_ge {k : ℕ} (t : TreeDecomp G) :
    (∃ w : t.W, #(t.𝓧 w) - 1 ≥ k) → t.ewidth ≥ k :=
  fun ⟨w, hw⟩ ↦ le_iSup_of_le w (by exact_mod_cast hw)

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

/-- Transport a tree decomposition along a graph isomorphism by mapping each bag. -/
noncomputable def TreeDecomp.map (φ : G ≃g G') (t : G.TreeDecomp) : G'.TreeDecomp := { t with
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
lemma TreeDecomp.ewidth_map (φ : G ≃g G') (t : G.TreeDecomp) : (t.map φ).ewidth = t.ewidth := by
  simp only [TreeDecomp.ewidth_eq, TreeDecomp.map, Finset.card_map]

lemma Iso.hasTreeDecomp_iff {n : ℕ∞} {V' : Type u}
    {G : SimpleGraph V} {G' : SimpleGraph V'} (φ : G ≃g G') :
    G.hasTreeDecomp n ↔ G'.hasTreeDecomp n :=
  ⟨fun ⟨t, ht⟩ ↦ ⟨t.map φ, TreeDecomp.ewidth_map φ t ▸ ht⟩,
   fun ⟨t, ht⟩ ↦ ⟨t.map φ.symm, TreeDecomp.ewidth_map φ.symm t ▸ ht⟩⟩

@[simp]
lemma TreeDecomp.coe_width {t : TreeDecomp G} (h : t.ewidth ≠ ⊤) :
    (t.width : ℕ∞) = t.ewidth := ENat.coe_toNat h

lemma TreeDecomp.card_bag_le_width (t : G.TreeDecomp) (hw : t.ewidth ≠ ⊤) (w : t.W) :
    #(t.𝓧 w) ≤ t.width + 1 := by
  have := t.card_bag_le w
  rw [← t.coe_width hw] at this
  exact_mod_cast this

/-- The tree decomposition obtained by putting all vertices in one bag. -/
def trivialTreeDecomp [Fintype V] (G : SimpleGraph V) : G.TreeDecomp where
  W := ULift.{u} Unit
  𝓧 := fun _ ↦ univ
  T := ⊥
  isTree := by exact IsTree.of_subsingleton
  vertexCover := by simp
  edgeCover := by simp
  connectedBags := by aesop_graph

lemma ewidth_trivialTreeDecomp [Fintype V] :
    (G.trivialTreeDecomp).ewidth = (card V - 1 : ℕ) := by
  simp [TreeDecomp.ewidth_eq, trivialTreeDecomp]

/-- The tree decomposition of `⊥` indexed by `Option V` with a star graph rooted at `none`:
bags are `∅` at `none` and `{v}` at `some v`. -/
noncomputable def botTreeDecomp : (⊥ : SimpleGraph V).TreeDecomp where
  W := Option V
  𝓧 w := w.elim ∅ ({·})
  T := starGraph none
  isTree := isTree_starGraph _
  vertexCover v := ⟨some v, by simp⟩
  edgeCover _ _ h := h.elim
  connectedBags v := by
    have : {w : Option V | v ∈ w.elim ∅ ({·} : V → Finset V)} = {some v} := by
      ext w
      cases w <;> simp [eq_comm]
    exact this ▸ Preconnected.of_subsingleton

lemma ewidth_botTreeDecomp : (botTreeDecomp (V := V)).ewidth = 0 := by
  refine iSup_eq_bot.mpr ?_
  rintro (_ | w) <;> simp [botTreeDecomp]

/-- If G has a tree decomposition of width n, then the same decomposition on any subgraph. -/
@[mono]
lemma TreeDecomp.mono {G' : SimpleGraph V} {n : ℕ∞} (h : G' ≤ G) (hG : G.hasTreeDecomp n) :
    G'.hasTreeDecomp n := by
  obtain ⟨t, ht⟩ := hG
  exact ⟨{ t with edgeCover := fun _ _ huv ↦ t.edgeCover (h huv)}, ht⟩

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

@[simp]
lemma TreeDecomp.width_le_iff_ewidth_le [Finite V] (t : TreeDecomp G) {k : ℕ} :
    t.width ≤ k ↔ t.ewidth ≤ k := by
  rw [← t.coe_width_of_finite]; exact_mod_cast Iff.rfl

/-- On a finite vertex type, every tree decomposition has width at most `card V - 1`. -/
lemma TreeDecomp.width_le_card [Fintype V] (t : TreeDecomp G) :
    t.width ≤ card V - 1 := by
  exact_mod_cast t.coe_width_of_finite ▸ t.ewidth_le_card

/-- Each bag of a tree decomposition has cardinality at most `width + 1` (finite-vertex form). -/
lemma TreeDecomp.card_bag_le_width_of_finite [Finite V] (t : G.TreeDecomp) (w : t.W) :
    #(t.𝓧 w) ≤ t.width + 1 := t.card_bag_le_width t.ewidth_ne_top_of_finite w

end TreeDecomp

/-! ## Tree width -/

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
  exact absurd (this.trans h) (by exact_mod_cast Nat.not_succ_le_self k)

@[simp]
lemma etreeWidth_ge_iff {k : ℕ∞} : G.etreeWidth ≥ k ↔ ∀ t : G.TreeDecomp, t.ewidth ≥ k := by
  contrapose!; exact iInf_lt_iff

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
  rw [← coe_treeWidth_of_finite]; exact_mod_cast Iff.rfl

/-- G has treewidth at most `k` (as a natural number) iff it has a tree decomposition of width
at most `k`. -/
theorem treeWidth_le_iff_hasTreeDecomp [Finite V] (k : ℕ) :
    G.treeWidth ≤ k ↔ G.hasTreeDecomp k :=
  treeWidth_le_iff_etreeWidth_le.trans (etreeWidth_le_iff_hasTreeDecomp k)

@[simp]
lemma treeWidth_ge_iff [Finite V] {k : ℕ} :
    G.treeWidth ≥ k ↔ ∀ t : G.TreeDecomp, t.width ≥ k := by
  simp [ge_iff_le, ← Nat.cast_le (α := ℕ∞)]

/-- The treewidth of a finite graph is at most `card V - 1`. -/
theorem treeWidth_le_card [Fintype V] : G.treeWidth ≤ card V - 1 :=
  treeWidth_le_iff_etreeWidth_le.mpr etreeWidth_le_card

@[gcongr]
lemma treeWidth_mono {G' : SimpleGraph V} [Finite V] (h : G' ≤ G) : G'.treeWidth ≤ G.treeWidth := by
  simpa using etreeWidth_mono h

/-- The treewidth of a graph is nonzero iff it has an edge. -/
theorem etreeWidth_ne_zero_iff_ne_bot : 0 < G.etreeWidth ↔ G ≠ ⊥ := by
  classical
  rw [← Order.one_le_iff_pos, ← ge_iff_le, etreeWidth_ge_iff]
  refine ⟨?_, ?_⟩
  · contrapose!
    rintro rfl
    exact ⟨botTreeDecomp, by rw [ewidth_botTreeDecomp]; decide⟩
  · rw [SimpleGraph.ne_bot_iff_exists_adj]
    rintro ⟨u, v, huv⟩ t
    obtain ⟨w, hu, hv⟩ := t.edgeCover huv
    have := Finset.one_lt_card.mpr ⟨u, hu, v, hv, huv.ne⟩
    exact_mod_cast t.ewidth_ge ⟨w, by omega⟩

lemma treeWidth_bot : (⊥ : SimpleGraph V).treeWidth = 0 := by
  have : (⊥ : SimpleGraph V).etreeWidth = 0 :=
    le_antisymm ((treeDecomp_imp_etreeWidth_le botTreeDecomp).trans ewidth_botTreeDecomp.le)
      (zero_le _)
  simp [treeWidth, this]

private lemma TreeDecomp.exists_bag_univ_of_forall_edgeCover [Nonempty V] [Fintype V]
    (t : G.TreeDecomp)
    (h : ∀ u v : V, ∃ w : t.W, u ∈ t.𝓧 w ∧ v ∈ t.𝓧 w) : ∃ w : t.W, t.𝓧 w = univ := by
  let f (x : V) := {w | x ∈ t.𝓧 w}
  have h_conn : ∀ i ∈ (univ : Finset V), (t.T.induce (f i)).Connected := fun v _ => by
    rw [connected_iff]
    obtain ⟨w, hw⟩ := t.vertexCover v
    exact ⟨t.connectedBags v, ⟨⟨w, hw⟩⟩⟩
  obtain ⟨w, hw⟩ := t.isTree.inter_nonempty_of_pairwise Finset.univ_nonempty h_conn
    (fun i _ j _ ↦ h i j)
  refine ⟨w, Finset.eq_univ_iff_forall.mpr ?_⟩
  simpa [f] using hw

theorem treewidth_top [Fintype V] : (⊤ : SimpleGraph V).treeWidth = card V - 1 := by
  refine le_antisymm treeWidth_le_card ?_
  rcases isEmpty_or_nonempty V with hV | hV
  · simp
  -- For ⊤, every pair has a common bag; some bag is the whole vertex set.
  simp only [ge_iff_le, treeWidth_ge_iff]
  intro t
  have forall_edgeCover : ∀ u v : V, ∃ w : t.W, u ∈ t.𝓧 w ∧ v ∈ t.𝓧 w := fun u v => by
    by_cases h : u = v
    · subst h; obtain ⟨w, hw⟩ := t.vertexCover u; exact ⟨w, hw, hw⟩
    · exact t.edgeCover ((top_adj u v).mpr h)
  obtain ⟨w, hw⟩ := t.exists_bag_univ_of_forall_edgeCover forall_edgeCover
  have h_contra := t.card_bag_le_width_of_finite w
  rw [hw, Finset.card_univ] at h_contra
  omega

end TreeWidth

namespace TreeDecomp
section Adhesion

/-- Given a tree decomposition (𝓧, T), the adhesion set is the intersection of bags along some edge
  in T. -/
@[nolint unusedArguments]
def adhesion [DecidableEq V] (t : G.TreeDecomp) {x y : t.W} (_ : t.T.Adj x y)
    : Finset V := (t.𝓧 x) ∩ (t.𝓧 y)

@[simp]
lemma mem_adhesion [DecidableEq V] (t : G.TreeDecomp) {x y : t.W} (adj : t.T.Adj x y)
    {v : V} : v ∈ t.adhesion adj ↔ v ∈ t.𝓧 x ∧ v ∈ t.𝓧 y := by
  simp [adhesion]

@[simp]
lemma not_mem_adhesion [DecidableEq V] (t : G.TreeDecomp) {x y : t.W} (adj : t.T.Adj x y)
    {v : V} : v ∉ t.adhesion adj ↔ v ∉ t.𝓧 x ∨ v ∉ t.𝓧 y := by
  simp only [mem_adhesion, not_and_or]

/-- The "induced separation" on V of one side of a cut tree edge: the union of bags on that
side, minus the adhesion. Parametrized by a side vertex `z : t.W`. -/
def inducedSeparation [DecidableEq V] (t : G.TreeDecomp) {x y : t.W}
    (hadj : t.T.Adj x y) (z : t.W) : Set V :=
  (⋃ w ∈ (t.T.subtreeOfCut t.isTree {s(x, y)} z).supp, (t.𝓧 w : Set V)) \ t.adhesion hadj

/-
@[simp]
lemma mem_inducedSeparation [DecidableEq V] (t : G.TreeDecomp) {x y : t.W}
    (hadj : t.T.Adj x y) (z : t.W) {v : V} : v ∈ t.inducedSeparation hadj z ↔
-/
-- TODO: Restate using subtree notation.
/-- If v is not in an adhesion set, all bags containing v must reside in some subtree cut by the
    adhesion set's edge.
-/
theorem adhesion_imp_separator [DecidableEq V] (t : G.TreeDecomp) {x y : t.W} (h : t.T.Adj x y) :
    ∀ v ∉ t.adhesion h, ∀ a b : t.W, v ∈ t.𝓧 a → v ∈ t.𝓧 b →
    ∀ p : t.T.Path a b, s(x, y) ∉ p.val.edges := by
  classical
  intro v hv a b ha hb p hxy
  obtain ⟨q⟩ := t.connectedBags v ⟨a, ha⟩ ⟨b, hb⟩
  let q' : t.T.Walk a b := q.map (Embedding.induce _).toHom
  have hpath : q'.toPath = p := t.isTree.isAcyclic.path_unique _ _
  have hq_support : ∀ w ∈ q'.support, v ∈ t.𝓧 w := by
    change ∀ w ∈ (q.map (Embedding.induce _).toHom).support, v ∈ t.𝓧 w
    simp only [Walk.support_map, List.mem_map]
    rintro w ⟨⟨w', hw'⟩, _, rfl⟩
    exact hw'
  have hp_sub : p.val.support ⊆ q'.support := hpath ▸ Walk.support_toPath_subset q'
  exact hv ((t.mem_adhesion h).mpr
    ⟨hq_support x (hp_sub (p.val.fst_mem_support_of_mem_edges hxy)),
     hq_support y (hp_sub (p.val.snd_mem_support_of_mem_edges hxy))⟩)

/-- If t is a tree decomposition with finite width, then either some bag contains every element,
or there is a proper adhesion set between two distinct bags. -/
theorem exists_proper_adhesion [Nonempty V] [DecidableEq V] (t : G.TreeDecomp)
    (hw : t.ewidth ≠ ⊤) :
    t.width + 1 = Nat.card V ∨ ∃ x y : t.W, ∃ h : t.T.Adj x y, #(t.adhesion h) ≤ t.width := by
  by_cases! h : ∀ x y : t.W, t.𝓧 x = t.𝓧 y
  · /- Because of h and t.vertexCover, every bag must contain V.univ -/
    left
    obtain w₀ := t.isTree.connected.nonempty.some
    have h_univ : ∀ v : V, v ∈ t.𝓧 w₀ := fun v => by
      obtain ⟨w, hw⟩ := t.vertexCover v
      exact (h w₀ w).symm ▸ hw
    rcases finite_or_infinite V with hV | hV
    · replace hV := Fintype.ofFinite V
      rw [Nat.card_eq_fintype_card]
      have hcard : #(t.𝓧 w₀) = Fintype.card V := by
        rw [Finset.eq_univ_of_forall h_univ, Finset.card_univ]
      have hle : Fintype.card V ≤ t.width + 1 := hcard ▸ t.card_bag_le_width hw w₀
      have hge : t.width ≤ Fintype.card V - 1 := t.width_le_card
      have hpos : 1 ≤ Fintype.card V := Fintype.card_pos
      omega
    /- Absurd because each bag is a finset. -/
    · obtain ⟨v, hv⟩ := Infinite.exists_notMem_finset (t.𝓧 w₀)
      exact absurd (h_univ v) hv
  · right
    obtain ⟨x, y, hxy⟩ := h
    obtain ⟨p⟩ := t.isTree.connected x y
    obtain ⟨d, _, hfst, hsnd⟩ := p.exists_boundary_dart {w | t.𝓧 w = t.𝓧 x} rfl hxy.symm
    have huv : t.𝓧 d.fst ≠ t.𝓧 d.snd := fun heq => hsnd (heq.symm.trans hfst)
    refine ⟨d.fst, d.snd, d.adj, ?_⟩
    rw [adhesion]
    have hbu := t.card_bag_le_width hw d.fst
    have hbv := t.card_bag_le_width hw d.snd
    by_cases h_sub : t.𝓧 d.fst ⊆ t.𝓧 d.snd
    · rw [Finset.inter_eq_left.mpr h_sub]
      have := Finset.card_lt_card (h_sub.ssubset_of_ne huv)
      omega
    · obtain ⟨z, hzu, hzv⟩ := Finset.not_subset.mp h_sub
      have := Finset.card_lt_card (Finset.ssubset_iff_of_subset
        Finset.inter_subset_left |>.mpr ⟨z, hzu, fun h => hzv (Finset.mem_inter.mp h).2⟩)
      omega

theorem disjoint_inducedSeparation [DecidableEq V] (t : G.TreeDecomp) {x y : t.W}
    (hadj : t.T.Adj x y) :
    Disjoint (t.inducedSeparation hadj x) (t.inducedSeparation hadj y) := by
  rw [Set.disjoint_left]
  intro v hvx hvy
  simp only [TreeDecomp.inducedSeparation, Set.mem_diff, Set.mem_iUnion₂] at hvx hvy
  obtain ⟨⟨w₁, hw₁_supp, hv₁⟩, hv_not_adh⟩ := hvx
  obtain ⟨⟨w₂, hw₂_supp, hv₂⟩, _⟩ := hvy
  obtain ⟨p, hp_path, _⟩ := t.isTree.existsUnique_path w₁ w₂
  exact adhesion_imp_separator t hadj v hv_not_adh w₁ w₂ hv₁ hv₂ ⟨p, hp_path⟩
    (t.T.path_mem_cut_edge_of_subtreeOfCut_ne t.isTree
      (fun h => t.T.disjoint_subtreeOfCut t.isTree hadj
        ((hw₁_supp : _ = _).symm.trans (h.trans hw₂_supp))) ⟨p, hp_path⟩)

/-- If u, v are in the induced separation from an edge, any walk between u, v contains some node in
    the adhesion set. -/
lemma mem_adhesion_of_inducedSeparation_walk [DecidableEq V] (t : G.TreeDecomp)
    {x y : t.W} (adj : t.T.Adj x y) : ∀ u ∈ t.inducedSeparation adj x,
    ∀ v ∈ t.inducedSeparation adj y, ∀ walk : G.Walk u v, walk.toSubgraph.verts ∩ t.adhesion adj ≠ ∅
    := by
  intro u hu v hv walk
  by_contra h
  -- v ∉ inducedSeparation adj x by disjointness
  have hv_notin : v ∉ t.inducedSeparation adj x :=
    Set.disjoint_right.mp (t.disjoint_inducedSeparation adj) hv
  -- Boundary dart d : d.fst ∈ inducedSeparation x, d.snd ∉ inducedSeparation x
  obtain ⟨d, hd_in, hd_fst_in, hd_snd_notin⟩ :=
    walk.exists_boundary_dart (t.inducedSeparation adj x) hu hv_notin
  -- Both endpoints of d lie on the walk
  have hd_fst_walk : d.fst ∈ walk.toSubgraph.verts :=
    walk.mem_verts_toSubgraph.mpr (walk.dart_fst_mem_support_of_mem_darts hd_in)
  have hd_snd_walk : d.snd ∈ walk.toSubgraph.verts :=
    walk.mem_verts_toSubgraph.mpr (walk.dart_snd_mem_support_of_mem_darts hd_in)
  -- By `h`, neither endpoint is in adhesion
  have hd_fst_not_adh : d.fst ∉ ↑(t.adhesion adj) := fun h_adh =>
    Set.notMem_empty d.fst (h ▸ ⟨hd_fst_walk, h_adh⟩)
  have hd_snd_not_adh : d.snd ∉ ↑(t.adhesion adj) := fun h_adh =>
    Set.notMem_empty d.snd (h ▸ ⟨hd_snd_walk, h_adh⟩)
  -- Some bag w₀ contains both d.fst and d.snd
  obtain ⟨w₀, h_d_fst_w₀, h_d_snd_w₀⟩ := t.edgeCover d.adj
  -- w₀'s component is either the x-side or the y-side
  rcases t.T.subtreeOfCut_eq_or_eq t.isTree adj w₀ with hw₀_x | hw₀_y
  · -- x-side: d.snd ∈ ⋃ subtreeOfCut x bags + ∉ adhesion ⇒ d.snd ∈ inducedSep x, contradicting
    exact hd_snd_notin
      ⟨Set.mem_iUnion₂.mpr ⟨w₀, hw₀_x, h_d_snd_w₀⟩, hd_snd_not_adh⟩
  · -- y-side: d.fst ∈ ⋃ subtreeOfCut y bags + ∉ adhesion ⇒ d.fst ∈ inducedSep y,
    -- contradicting hd_fst_in via disjointness
    exact Set.disjoint_left.mp (t.disjoint_inducedSeparation adj) hd_fst_in
      ⟨Set.mem_iUnion₂.mpr ⟨w₀, hw₀_y, h_d_fst_w₀⟩, hd_fst_not_adh⟩

/- TODO: Golf this or remove if unnecessary. -/
lemma connected_walk (t : G.TreeDecomp) {u v : V} (walk : G.Walk u v) :
    (t.T.induce {w | (walk.toSubgraph.verts ∩ t.𝓧 w).Nonempty}).Preconnected := by
  induction walk with
  | nil =>
    expose_names
    convert t.connectedBags u_1 using 2 <;>
      · ext w
        simp [Walk.toSubgraph, singletonSubgraph_verts, Set.singleton_inter_nonempty]
  | @cons u v w h_adj p ih =>
    obtain ⟨w₀, hu₀, hv₀⟩ := t.edgeCover h_adj
    have hSp_pre : (t.T.induce {w_1 | (p.toSubgraph.verts ∩ ↑(t.𝓧 w_1)).Nonempty}).Preconnected :=
      ih
    have hSu_pre : (t.T.induce {w_1 | u ∈ t.𝓧 w_1}).Preconnected := t.connectedBags u
    have hinter : ({w_1 | (p.toSubgraph.verts ∩ ↑(t.𝓧 w_1)).Nonempty} ∩ {w_1 | u ∈ t.𝓧 w_1}
                  : Set t.W).Nonempty :=
      ⟨w₀, ⟨v, p.start_mem_verts_toSubgraph, hv₀⟩, hu₀⟩
    have hcon := induce_union_connected hSp_pre hSu_pre hinter
    have heq : {w_1 | ((Walk.cons h_adj p).toSubgraph.verts ∩ ↑(t.𝓧 w_1)).Nonempty}
        = {w_1 | (p.toSubgraph.verts ∩ ↑(t.𝓧 w_1)).Nonempty} ∪ {w_1 | u ∈ t.𝓧 w_1} := by
      ext w'
      simp only [Set.mem_setOf_eq, Set.mem_union, Walk.toSubgraph, Subgraph.verts_sup,
        subgraphOfAdj_verts, Set.union_inter_distrib_right, Set.union_nonempty,
        Set.insert_eq, Set.singleton_inter_nonempty]
      constructor
      · rintro ((hu | hv) | hp)
        · exact Or.inr hu
        · exact Or.inl ⟨v, p.start_mem_verts_toSubgraph, hv⟩
        · exact Or.inl hp
      · rintro (hp | hu)
        · exact Or.inr hp
        · exact Or.inl (Or.inl hu)
    rw [heq]
    exact hcon.preconnected

end Adhesion
end TreeDecomp

end SimpleGraph
