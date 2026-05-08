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

- isSeparator_walk_cover : s is a (u, v)-separator if any walk from u to v visits s

## Tags

-/

@[expose] public section

namespace SimpleGraph

open Subgraph

variable {V V' : Type*} (G : SimpleGraph V) (G' : SimpleGraph V')

variable {s : Set V} {u v : V}

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
    exact (p.induce sᶜ fun x hx hxs =>
      Set.notMem_empty x (hp ▸ ⟨(Walk.mem_verts_toSubgraph p).mpr hx, hxs⟩)).reachable

theorem not_isSeparator_iff :
    ¬G.IsSeparator s u v ↔ u ∈ s ∨ v ∈ s ∨ ∃ (walk : G.Walk u v),
    walk.toSubgraph.verts ∩ s = ∅ := by
  simp only [isSeparator_iff, not_exists, not_not]
  by_cases hu : u ∈ s
  · exact iff_of_true (fun h => (h hu).elim) (.inl hu)
  by_cases hv : v ∈ s
  · exact iff_of_true (fun _ h => (h hv).elim) (.inr (.inl hv))
  simp [hu, hv, G.reachable_induce_compl_iff hu hv]

lemma isSeparator_empty : G.IsSeparator ∅ u v ↔ ¬G.Reachable u v := by
  suffices h : (G.induce ∅ᶜ).Reachable ⟨u, Set.notMem_empty u⟩ ⟨v, Set.notMem_empty v⟩ ↔
      G.Reachable u v by
    simp [isSeparator_iff, h]
  exact ⟨fun h => h.map (Embedding.induce ∅ᶜ).toHom,
    fun h => (h.some.induce _ fun _ _ => Set.notMem_empty _).reachable⟩

lemma isSeparator_iff_walk_cover :
    G.IsSeparator s u v ↔
      u ∉ s ∧ v ∉ s ∧ ∀ walk : G.Walk u v, ∃ si ∈ s, si ∈ walk.toSubgraph.verts := by
  rw [← not_iff_not, not_isSeparator_iff]
  push Not
  simp [Set.eq_empty_iff_forall_notMem, Set.mem_inter_iff, and_comm]
  tauto


end SimpleGraph
