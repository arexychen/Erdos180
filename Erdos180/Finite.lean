import Erdos180.Extremal

open Filter
open Asymptotics

noncomputable section

namespace Erdos180

universe u v w

/-- A finite graph packaged with its vertex type. -/
structure FiniteSimpleGraph where
  V : Type u
  instFintype : Fintype V
  graph : SimpleGraph V

namespace FiniteSimpleGraph

instance (X : FiniteSimpleGraph.{u}) : Fintype X.V :=
  X.instFintype

/-- The non-isolated part of a packaged graph. -/
abbrev reduced (X : FiniteSimpleGraph.{u}) : SimpleGraph X.graph.support :=
  deleteIsolated X.graph

/-- The extremal function of a packaged graph. -/
def extremal (X : FiniteSimpleGraph.{u}) (n : ℕ) : ℕ :=
  extremalNumber X.graph n

/-- The reduced graph is a forest. -/
def forestAfterDeletingIsolated (X : FiniteSimpleGraph.{u}) : Prop :=
  X.reduced.IsAcyclic

/-- The reduced graph has at least two edges. -/
def atLeastTwoEdgesAfterDeletingIsolated (X : FiniteSimpleGraph.{u}) : Prop :=
  2 ≤ edgeCount X.reduced

/-- The reduced graph is a star. -/
def starAfterDeletingIsolated (X : FiniteSimpleGraph.{u}) : Prop :=
  IsStar X.reduced

/-- The reduced graph is a matching. -/
def matchingAfterDeletingIsolated (X : FiniteSimpleGraph.{u}) : Prop :=
  IsMatchingGraph X.reduced

def starWithAtLeastTwoEdgesAfterDeletingIsolated
    (X : FiniteSimpleGraph.{u}) : Prop :=
  X.starAfterDeletingIsolated ∧ X.atLeastTwoEdgesAfterDeletingIsolated

def matchingWithAtLeastTwoEdgesAfterDeletingIsolated
    (X : FiniteSimpleGraph.{u}) : Prop :=
  X.matchingAfterDeletingIsolated ∧ X.atLeastTwoEdgesAfterDeletingIsolated

end FiniteSimpleGraph

/--
Logic hub: every nonempty subgraph of a star is a star after deleting isolated
vertices.
-/
theorem nonempty_subgraph_of_star_deleteIsolated_isStar
    {V : Type u} {G : SimpleGraph V}
    (hG : IsStar G)
    (S : G.Subgraph)
    (hne : ∃ x y : V, S.Adj x y) :
    IsStar (deleteIsolated S.coe) := by
  rcases hG with ⟨c, rfl⟩
  rcases hne with ⟨x, y, hxy⟩
  have hxy_star : (starGraph c).Adj x y := S.adj_sub hxy
  have hc_verts : c ∈ S.verts := by
    rcases hxy_star with h | h
    · simpa [h.1] using S.edge_vert hxy
    · simpa [h.1] using S.edge_vert hxy.symm
  let cS : S.verts := ⟨c, hc_verts⟩
  have hc_support : cS ∈ S.coe.support := by
    rw [SimpleGraph.mem_support]
    rcases hxy_star with h | h
    · refine ⟨⟨y, S.edge_vert hxy.symm⟩, ?_⟩
      simpa [cS, h.1] using hxy
    · refine ⟨⟨x, S.edge_vert hxy⟩, ?_⟩
      simpa [cS, h.1] using hxy.symm
  let center : S.coe.support := ⟨cS, hc_support⟩
  have eq_center_of_val_eq
      (z : S.coe.support) (hz : ((z : S.verts) : V) = c) :
      z = center := by
    apply Subtype.ext
    apply Subtype.ext
    exact hz
  have val_ne_of_ne_center
      (z : S.coe.support) (hz : z ≠ center) :
      ((z : S.verts) : V) ≠ c := by
    intro hzv
    exact hz (eq_center_of_val_eq z hzv)
  have adj_center_of_ne_center
      (z : S.coe.support) (hz : z ≠ center) :
      S.coe.Adj center.1 z.1 := by
    rcases z.2 with ⟨w, hzw⟩
    have hzw_star : (starGraph c).Adj ((z : S.verts) : V) (w : V) :=
      S.adj_sub hzw
    rcases hzw_star with h | h
    · exact False.elim ((val_ne_of_ne_center z hz) h.1)
    · have hw_eq : w = center.1 := by
        apply Subtype.ext
        exact h.1
      have hzc : S.coe.Adj z.1 center.1 := by
        simpa [hw_eq] using hzw
      exact hzc.symm
  refine ⟨center, ?_⟩
  ext u v
  constructor
  · intro huv
    have huvS : S.coe.Adj u.1 v.1 := by
      simpa [deleteIsolated] using huv
    have huv_star : (starGraph c).Adj ((u : S.verts) : V) ((v : S.verts) : V) :=
      S.adj_sub huvS
    rcases huv_star with h | h
    · have hu : u = center := eq_center_of_val_eq u h.1
      exact Or.inl ⟨hu, by
        intro hv
        exact huv.ne (hu.trans hv.symm)⟩
    · have hv : v = center := eq_center_of_val_eq v h.1
      exact Or.inr ⟨hv, by
        intro hu
        exact huv.ne (hu.trans hv.symm)⟩
  · intro huv
    rcases huv with h | h
    · rcases h with ⟨hu, hv_ne⟩
      subst hu
      have hcv : S.coe.Adj center.1 v.1 :=
        adj_center_of_ne_center v hv_ne
      simpa [deleteIsolated] using hcv
    · rcases h with ⟨hv, hu_ne⟩
      subst hv
      have hcu : S.coe.Adj center.1 u.1 :=
        adj_center_of_ne_center u hu_ne
      simpa [deleteIsolated] using hcu.symm

/-- If a vertex has at least `a` neighbors, then the canonical `a`-leaf star
embeds into the graph.  The center is `none`; the leaves are indexed by
`some i`, with `i : Fin a`. -/
theorem star_embedding_of_degree_ge
    {V : Type u} (G : SimpleGraph V) (v : V)
    [Fintype (G.neighborSet v)]
    {a : ℕ} (hdeg : a ≤ G.degree v) :
    EmbedsAsSubgraph (starGraph (none : Option (Fin a))) G := by
  classical
  have hcard : Fintype.card (Fin a) ≤ Fintype.card (G.neighborSet v) := by
    simpa using hdeg
  rcases Function.Embedding.nonempty_of_card_le hcard with
    ⟨leaf : Fin a ↪ G.neighborSet v⟩
  let f : Option (Fin a) → V := fun x =>
    match x with
    | none => v
    | some i => leaf i
  refine ⟨f, ?_, ?_⟩
  · intro x y hxy
    cases x with
    | none =>
        cases y with
        | none => rfl
        | some j =>
            exfalso
            have hadj : G.Adj v (leaf j : V) := (leaf j).property
            exact hadj.ne hxy
    | some i =>
        cases y with
        | none =>
            exfalso
            have hadj : G.Adj v (leaf i : V) := (leaf i).property
            exact hadj.ne hxy.symm
        | some j =>
            congr
            exact leaf.injective (Subtype.ext hxy)
  · intro x y hxy
    rcases hxy with h | h
    · rcases h with ⟨hx, hy⟩
      subst hx
      cases y with
      | none => exact False.elim (hy rfl)
      | some j =>
          exact (leaf j).property
    · rcases h with ⟨hy, hx⟩
      subst hy
      cases x with
      | none => exact False.elim (hx rfl)
      | some i =>
          exact ((leaf i).property).symm

end Erdos180
