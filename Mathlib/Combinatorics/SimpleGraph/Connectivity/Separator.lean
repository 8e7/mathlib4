/-
Copyright (c) 2026 Justin Lai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justin Lai
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Combinatorics.SimpleGraph.Subgraph
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!

# Graph Separators

## Main definitions

- `SimpleGraph.IsSeparator s u v` : Predicate that set s separates vertices u, v.
  Note that u ∉ s, v ∉ s must be satisfied.

## Main statements

- isSeparator_iff_walk_cover : s is a (u, v)-separator if any walk from u to v visits s

## Tags

-/

@[expose] public section

namespace SimpleGraph

open Subgraph

variable {V V' : Type*} {G : SimpleGraph V} {G' : SimpleGraph V'}

variable {s : Set V} {u v : V}

/-- s is a separator of (u, v) if u is reachable to v after removing vertices from s. -/
def IsSeparator (s : Set V) (u v : V) : Prop :=
  ∃ (hu : u ∉ s) (hv : v ∉ s), ¬(G.induce sᶜ).Reachable ⟨u, hu⟩ ⟨v, hv⟩

lemma isSeparator_iff :
    G.IsSeparator s u v ↔ ∃ (hu : u ∉ s) (hv : v ∉ s), ¬(G.induce sᶜ).Reachable ⟨u, hu⟩ ⟨v, hv⟩ :=
  Iff.rfl

private lemma reachable_induce_compl_iff (hu : u ∉ s) (hv : v ∉ s) :
    (G.induce sᶜ).Reachable ⟨u, hu⟩ ⟨v, hv⟩ ↔
      ∃ p : G.Walk u v, p.toSubgraph.verts ∩ s = ∅ := by
  constructor
  · rintro ⟨hp⟩
    use hp.map (Embedding.induce sᶜ).toHom
    rw [Walk.verts_toSubgraph, Set.eq_empty_iff_forall_notMem]
    rintro x ⟨hmem, hxs⟩
    change x ∈ (hp.map (Embedding.induce sᶜ).toHom).support at hmem
    rw [Walk.support_map, List.mem_map] at hmem
    obtain ⟨⟨y, hy⟩, _, rfl⟩ := hmem
    exact hy hxs
  · rintro ⟨p, hp⟩
    exact (p.induce sᶜ fun x hx hxs ↦
      Set.notMem_empty x (hp ▸ ⟨(Walk.mem_verts_toSubgraph p).mpr hx, hxs⟩)).reachable

lemma isSeparator_iff_walk_cover :
    G.IsSeparator s u v ↔
      u ∉ s ∧ v ∉ s ∧ ∀ walk : G.Walk u v, ∃ si ∈ s, si ∈ walk.toSubgraph.verts := by
  simp_rw [isSeparator_iff, G.reachable_induce_compl_iff, not_exists, Set.inter_comm,
    ← Set.nonempty_iff_ne_empty, Set.inter_nonempty, exists_prop]

theorem not_isSeparator_iff :
    ¬G.IsSeparator s u v ↔ u ∈ s ∨ v ∈ s ∨ ∃ (walk : G.Walk u v),
    walk.toSubgraph.verts ∩ s = ∅ := by
  simp [isSeparator_iff_walk_cover, Set.eq_empty_iff_forall_notMem, Set.mem_inter_iff,
    imp_not_comm, or_iff_not_and_not]

lemma isSeparator_empty : G.IsSeparator ∅ u v ↔ ¬G.Reachable u v := by
  suffices h : (G.induce ∅ᶜ).Reachable ⟨u, Set.notMem_empty u⟩ ⟨v, Set.notMem_empty v⟩ ↔
      G.Reachable u v by
    simp [isSeparator_iff, h]
  exact ⟨fun h ↦ h.map (Embedding.induce ∅ᶜ).toHom,
    fun h ↦ (h.some.induce _ fun _ _ ↦ Set.notMem_empty _).reachable⟩

/-- Easy direction of Menger's theorem. The size of any `(u,v)`-separator is at
least the cardinality of any pairwise internally-disjoint family of `u`–`v` walks. -/
lemma IsSeparator.card_le_encard_of_walks (hs : G.IsSeparator s u v)
    (P : Finset (G.Walk u v))
    (hdisj : (P : Set (G.Walk u v)).Pairwise fun p₁ p₂ =>
      ∀ x ∈ p₁.toSubgraph.verts, x ∈ p₂.toSubgraph.verts → x = u ∨ x = v) :
    (P.card : ℕ∞) ≤ s.encard := by
  classical
  obtain ⟨hu, hv, hcov⟩ := G.isSeparator_iff_walk_cover.mp hs
  choose f hf_mem hf_walk using hcov
  have hinj : Set.InjOn f P := fun p₁ hp₁ p₂ hp₂ hfeq ↦ by
    by_contra hne
    have hxp2 : f p₁ ∈ p₂.toSubgraph.verts := hfeq.symm ▸ hf_walk p₂
    rcases hdisj hp₁ hp₂ hne (f p₁) (hf_walk p₁) hxp2 with h | h
    · exact hu (h ▸ hf_mem p₁)
    · exact hv (h ▸ hf_mem p₁)
  rw [← Set.encard_coe_eq_coe_finsetCard, ← hinj.encard_image]
  exact Set.encard_le_encard (Set.image_subset_iff.mpr fun p _ ↦ hf_mem p)

lemma two_le_card_separator_of_disjoint_walks {p₁ p₂ : G.Walk u v}
    (hdisj : ∀ x ∈ p₁.toSubgraph.verts, x ∈ p₂.toSubgraph.verts → x = u ∨ x = v) :
    ∀ s : Finset V, G.IsSeparator s u v → 2 ≤ s.card := by
  intro s hs
  obtain ⟨hu, hv, hcov⟩ := G.isSeparator_iff_walk_cover.mp hs
  obtain ⟨s₁, hs₁, hp₁⟩ := hcov p₁
  obtain ⟨s₂, hs₂, hp₂⟩ := hcov p₂
  refine Finset.one_lt_card.mpr ⟨s₁, hs₁, s₂, hs₂, ?_⟩
  rintro rfl
  rcases hdisj s₁ hp₁ hp₂ with rfl | rfl
  · exact hu hs₁
  · exact hv hs₁

end SimpleGraph
