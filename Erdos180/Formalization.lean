import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Tactic

/-!
# Erdős Problem #180: formal scaffolding

This file formalizes the statements from the accompanying graph-theoretic proof.
The principal graph-theoretic construction bridges are named explicitly, and the
asymptotic dispatch around them is proved against the current mathlib API.
-/

open Filter
open Asymptotics

noncomputable section

namespace Erdos180

universe u v w

/-- Delete all isolated vertices of a graph.  In mathlib this is the induced
subgraph on `G.support`, the set of vertices incident to at least one edge. -/
abbrev deleteIsolated {V : Type u} (G : SimpleGraph V) : SimpleGraph G.support :=
  G.induce G.support

/-- The labelled star with center `c`. -/
def starGraph {V : Type u} (c : V) : SimpleGraph V where
  Adj x y := (x = c ∧ y ≠ c) ∨ (y = c ∧ x ≠ c)
  symm := by
    intro x y h
    exact h.elim (fun hxy => Or.inr hxy) (fun hyx => Or.inl hyx)
  loopless := by
    constructor
    intro x h
    rcases h with h | h
    · exact h.2 h.1
    · exact h.2 h.1

/-- A graph is a star if it is equal to a labelled star for some center. -/
def IsStar {V : Type u} (G : SimpleGraph V) : Prop :=
  ∃ c : V, G = starGraph c

/-- The canonical matching with `b` independent edges.  The edge with index
`i : Fin b` joins `(i, false)` to `(i, true)`. -/
def matchingGraph (b : ℕ) : SimpleGraph (Fin b × Bool) where
  Adj x y := x.1 = y.1 ∧ x.2 ≠ y.2
  symm := by
    intro x y h
    exact ⟨h.1.symm, h.2.symm⟩
  loopless := by
    constructor
    intro x h
    exact h.2 rfl

/-- A graph is a matching graph if no vertex is incident to two distinct neighbors. -/
def IsMatchingGraph {V : Type u} (G : SimpleGraph V) : Prop :=
  ∀ ⦃x y z : V⦄, G.Adj x y → G.Adj x z → y = z

/-- Ordinary, not necessarily induced, subgraph containment via an injective
edge-preserving map. -/
def EmbedsAsSubgraph {α : Type u} {β : Type v}
    (H : SimpleGraph α) (G : SimpleGraph β) : Prop :=
  ∃ f : α → β,
    Function.Injective f ∧
      ∀ ⦃x y : α⦄, H.Adj x y → G.Adj (f x) (f y)

/-- Subgraph embeddings compose. -/
theorem EmbedsAsSubgraph.trans
    {α : Type u} {β : Type v} {γ : Type w}
    {H : SimpleGraph α} {G : SimpleGraph β} {K : SimpleGraph γ}
    (hHG : EmbedsAsSubgraph H G) (hGK : EmbedsAsSubgraph G K) :
    EmbedsAsSubgraph H K := by
  rcases hHG with ⟨f, hf, hfmap⟩
  rcases hGK with ⟨g, hg, hgmap⟩
  exact ⟨g ∘ f, hg.comp hf, fun _ _ hxy => hgmap (hfmap hxy)⟩

/-- `G` is `H`-free for ordinary subgraph containment. -/
def IsHFree {α : Type u} {β : Type v}
    (H : SimpleGraph α) (G : SimpleGraph β) : Prop :=
  ¬ EmbedsAsSubgraph H G

/-- Edge count, expressed using `Nat.card` of the mathlib edge set. -/
def edgeCount {V : Type u} (G : SimpleGraph V) : ℕ :=
  Nat.card G.edgeSet

/-- The extremal number `ex(n; H)` for labelled `n`-vertex host graphs. -/
def extremalNumber {α : Type u} (H : SimpleGraph α) (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ G : SimpleGraph (Fin n), IsHFree H G ∧ edgeCount G = m}

/-- `f(n) = O(n)`. -/
def IsOLinear (f : ℕ → ℕ) : Prop :=
  (fun n : ℕ => (f n : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ))

/-- `f(n) = Ω(n)`. -/
def IsOmegaLinear (f : ℕ → ℕ) : Prop :=
  (fun n : ℕ => (n : ℝ)) =O[atTop] (fun n : ℕ => (f n : ℝ))

/-- `f(n) = Θ(n)`. -/
def IsThetaLinear (f : ℕ → ℕ) : Prop :=
  (fun n : ℕ => (f n : ℝ)) =Θ[atTop] (fun n : ℕ => (n : ℝ))

/-- `f(n) = O(1)`. -/
def IsOConstant (f : ℕ → ℕ) : Prop :=
  (fun n : ℕ => (f n : ℝ)) =O[atTop] (fun _ : ℕ => (1 : ℝ))

/-- `f(n) = Θ(1)`. -/
def IsThetaConstant (f : ℕ → ℕ) : Prop :=
  (fun n : ℕ => (f n : ℝ)) =Θ[atTop] (fun _ : ℕ => (1 : ℝ))

/-- A bounded natural-valued function is `O(1)`. -/
theorem isOConstant_of_forall_le (f : ℕ → ℕ) (C : ℕ)
    (hC : ∀ n, f n ≤ C) :
    IsOConstant f := by
  unfold IsOConstant
  refine IsBigO.of_bound (C : ℝ) (Filter.Eventually.of_forall ?_)
  intro n
  have hreal : (f n : ℝ) ≤ (C : ℝ) := by
    exact_mod_cast hC n
  simpa using hreal

/-- The natural-valued identity function is not `O(1)`. -/
lemma not_natCast_isBigO_one :
    ¬ ((fun n : ℕ => (n : ℝ)) =O[Filter.atTop] (fun _ : ℕ => (1 : ℝ))) := by
  intro h
  rcases h.bound with ⟨C, hC⟩
  rw [Filter.eventually_atTop] at hC
  rcases hC with ⟨N, hN⟩
  rcases exists_nat_gt (max C (N : ℝ)) with ⟨n, hn⟩
  have hnN_real : (N : ℝ) < (n : ℝ) :=
    lt_of_le_of_lt (le_max_right C (N : ℝ)) hn
  have hnN : N ≤ n := by
    exact_mod_cast (le_of_lt hnN_real)
  have hnC : C < (n : ℝ) :=
    lt_of_le_of_lt (le_max_left C (N : ℝ)) hn
  have hbound := hN n hnN
  have hle : (n : ℝ) ≤ C := by
    simpa using hbound
  exact not_lt_of_ge hle hnC

/-- A natural-valued function that is `O(1)` is not `Θ(n)`. -/
lemma not_isThetaLinear_of_isOConstant (f : ℕ → ℕ) :
    IsOConstant f → ¬ IsThetaLinear f := by
  intro hO hTheta
  unfold IsOConstant at hO
  unfold IsThetaLinear at hTheta
  exact not_natCast_isBigO_one (hTheta.isBigO_symm.trans hO)

/-- An eventually positive natural-valued function is bounded below by a
positive constant, asymptotically. -/
theorem isOmegaConstant_of_eventually_one_le (f : ℕ → ℕ)
    (hpos : ∀ᶠ n in atTop, 1 ≤ f n) :
    (fun _ : ℕ => (1 : ℝ)) =O[atTop] (fun n : ℕ => (f n : ℝ)) := by
  refine IsBigO.of_bound (1 : ℝ) ?_
  filter_upwards [hpos] with n hn
  have hreal : (1 : ℝ) ≤ (f n : ℝ) := by
    exact_mod_cast hn
  simpa using hreal

/-- A bounded natural-valued function that is eventually at least one is
`Θ(1)`. -/
theorem isThetaConstant_of_forall_le_of_eventually_one_le
    (f : ℕ → ℕ) (C : ℕ)
    (hC : ∀ n, f n ≤ C)
    (hpos : ∀ᶠ n in atTop, 1 ≤ f n) :
    IsThetaConstant f := by
  unfold IsThetaConstant
  exact ⟨isOConstant_of_forall_le f C hC,
    isOmegaConstant_of_eventually_one_le f hpos⟩

/-- Combine the two sides of a linear asymptotic estimate. -/
theorem isThetaLinear_of_isOLinear_of_isOmegaLinear
    (f : ℕ → ℕ) (hO : IsOLinear f) (hΩ : IsOmegaLinear f) :
    IsThetaLinear f := by
  unfold IsThetaLinear IsOLinear IsOmegaLinear at *
  exact ⟨hO, hΩ⟩

/-- If `f(n) ≥ n - 1` eventually, then `f(n) = Ω(n)`. -/
theorem isOmegaLinear_of_eventually_pred_le
    (f : ℕ → ℕ)
    (h : ∀ᶠ n in atTop, n - 1 ≤ f n) :
    IsOmegaLinear f := by
  unfold IsOmegaLinear
  refine IsBigO.of_bound (2 : ℝ) ?_
  filter_upwards [h, eventually_atTop.2 ⟨2, fun n hn => hn⟩] with n hpred hn2
  have hnat : n ≤ 2 * f n := by
    have hpred' : n ≤ 2 * (n - 1) := by omega
    exact hpred'.trans (Nat.mul_le_mul_left 2 hpred)
  have hreal : (n : ℝ) ≤ (2 : ℝ) * (f n : ℝ) := by
    exact_mod_cast hnat
  simpa using hreal

/-- If `f(n) ≥ ⌊n/2⌋` eventually, then `f(n) = Ω(n)`. -/
theorem isOmegaLinear_of_eventually_half_le
    (f : ℕ → ℕ)
    (h : ∀ᶠ n in atTop, n / 2 ≤ f n) :
    IsOmegaLinear f := by
  unfold IsOmegaLinear
  refine IsBigO.of_bound (4 : ℝ) ?_
  filter_upwards [h, eventually_atTop.2 ⟨2, fun n hn => hn⟩] with n hhalf hn2
  have hnat : n ≤ 4 * f n := by
    have hhalf' : n ≤ 4 * (n / 2) := by omega
    exact hhalf'.trans (Nat.mul_le_mul_left 4 hhalf)
  have hreal : (n : ℝ) ≤ (4 : ℝ) * (f n : ℝ) := by
    exact_mod_cast hnat
  simpa using hreal

/-- If every element of a set of natural numbers is at most `C`, then its
supremum is at most `C`.  This version also handles the empty set. -/
theorem nat_sSup_le_of_forall_le {s : Set ℕ} {C : ℕ}
    (hC : ∀ m ∈ s, m ≤ C) :
    sSup s ≤ C := by
  classical
  rw [Nat.sSup_def ⟨C, hC⟩]
  exact Nat.find_min' ⟨C, hC⟩ hC

/-- Membership in a bounded set of natural numbers gives a lower bound on its
supremum. -/
theorem nat_le_sSup_of_mem_of_forall_le {s : Set ℕ} {m C : ℕ}
    (hm : m ∈ s)
    (hC : ∀ x ∈ s, x ≤ C) :
    m ≤ sSup s := by
  exact le_csSup ⟨C, hC⟩ hm

/-- A graph on `n` labelled vertices has at most `n.choose 2` edges. -/
theorem edgeCount_le_complete_bound {n : ℕ}
    (G : SimpleGraph (Fin n)) :
    edgeCount G ≤ n.choose 2 := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel _
  have hedge : edgeCount G = G.edgeFinset.card := by
    rw [edgeCount, Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
  rw [hedge]
  simpa using (SimpleGraph.card_edgeFinset_le_card_choose_two (G := G))

/-- Any admissible host contributes a lower bound to the single-graph extremal
number. -/
theorem extremalNumber_ge_of_host {α : Type u}
    (H : SimpleGraph α) {n : ℕ}
    (G : SimpleGraph (Fin n))
    (hfree : IsHFree H G) :
    edgeCount G ≤ extremalNumber H n := by
  unfold extremalNumber
  refine nat_le_sSup_of_mem_of_forall_le (C := n.choose 2) ?_ ?_
  · exact ⟨G, hfree, rfl⟩
  · intro m hm
    rcases hm with ⟨G', _hfree, rfl⟩
    exact edgeCount_le_complete_bound G'

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

/-- If a graph contains a matching subgraph with at least `b` edges, then the
canonical `b`-edge matching embeds into the graph.  The proof explicitly
chooses an injection `Fin b ↪ M.edgeSet` and maps the two Boolean endpoints of
each index to the two endpoints of the selected edge. -/
theorem matching_embedding_of_card_ge
    {V : Type u} {G : SimpleGraph V}
    (M : G.Subgraph) (hM : M.IsMatching)
    [Fintype M.edgeSet]
    {b : ℕ} (hcard : b ≤ Fintype.card M.edgeSet) :
    EmbedsAsSubgraph (matchingGraph b) G := by
  classical
  have hcard' : Fintype.card (Fin b) ≤ Fintype.card M.edgeSet := by
    simpa using hcard
  rcases Function.Embedding.nonempty_of_card_le hcard' with
    ⟨edgeEmb : Fin b ↪ M.edgeSet⟩
  let left : Fin b → V := fun i => (edgeEmb i).val.out.1
  let right : Fin b → V := fun i => (edgeEmb i).val.out.2
  have edge_pair_eq (i : Fin b) :
      s(left i, right i) = (edgeEmb i).val := by
    change s((edgeEmb i).val.out.1, (edgeEmb i).val.out.2) = (edgeEmb i).val
    rw [Sym2.mk, (edgeEmb i).val.out_eq]
  have edge_adj (i : Fin b) : M.Adj (left i) (right i) := by
    change s(left i, right i) ∈ M.edgeSet
    rw [edge_pair_eq i]
    exact (edgeEmb i).property
  let L : Fin b → M.verts := fun i =>
    ⟨left i, M.edge_vert (edge_adj i)⟩
  let R : Fin b → M.verts := fun i =>
    ⟨right i, M.edge_vert (edge_adj i).symm⟩
  let endpoint : Fin b → Bool → M.verts := fun i side =>
    if side then R i else L i
  have selected_endpoint (i : Fin b) (side : Bool) :
      hM.toEdge (endpoint i side) = edgeEmb i := by
    cases side
    · change hM.toEdge (L i) = edgeEmb i
      calc
        hM.toEdge (L i) =
            ⟨s(left i, right i), edge_adj i⟩ :=
          hM.toEdge_eq_of_adj (M.edge_vert (edge_adj i)) (edge_adj i)
        _ = edgeEmb i := by
          apply Subtype.ext
          exact edge_pair_eq i
    · change hM.toEdge (R i) = edgeEmb i
      calc
        hM.toEdge (R i) =
            ⟨s(right i, left i), (edge_adj i).symm⟩ :=
          hM.toEdge_eq_of_adj
            (M.edge_vert (edge_adj i).symm) (edge_adj i).symm
        _ = edgeEmb i := by
          apply Subtype.ext
          calc
            s(right i, left i) = s(left i, right i) := Sym2.eq_swap
            _ = (edgeEmb i).val := edge_pair_eq i
  have edge_eq_of_endpoint_eq
      {i j : Fin b} {si sj : Bool}
      (h : (endpoint i si : V) = (endpoint j sj : V)) :
      edgeEmb i = edgeEmb j := by
    calc
      edgeEmb i = hM.toEdge (endpoint i si) := (selected_endpoint i si).symm
      _ = hM.toEdge (endpoint j sj) := by
        exact congrArg hM.toEdge (Subtype.ext h)
      _ = edgeEmb j := selected_endpoint j sj
  let f : Fin b × Bool → V := fun p => endpoint p.1 p.2
  refine ⟨f, ?_, ?_⟩
  · intro p q hpq
    rcases p with ⟨i, si⟩
    rcases q with ⟨j, sj⟩
    change (endpoint i si : V) = (endpoint j sj : V) at hpq
    have hedge : edgeEmb i = edgeEmb j :=
      edge_eq_of_endpoint_eq hpq
    have hij : i = j := edgeEmb.injective hedge
    subst j
    cases si <;> cases sj
    · rfl
    · exfalso
      have hbad : left i = right i := by
        simpa [endpoint, L, R] using hpq
      exact (edge_adj i).ne hbad
    · exfalso
      have hbad : right i = left i := by
        simpa [endpoint, L, R] using hpq
      exact (edge_adj i).ne hbad.symm
    · rfl
  · intro p q hpq
    rcases p with ⟨i, si⟩
    rcases q with ⟨j, sj⟩
    rcases hpq with ⟨hij, hne⟩
    have hij' : i = j := by
      simpa using hij
    subst j
    cases si <;> cases sj
    · exact False.elim (hne rfl)
    · simpa [f, endpoint, L, R] using M.adj_sub (edge_adj i)
    · simpa [f, endpoint, L, R] using (M.adj_sub (edge_adj i)).symm
    · exact False.elim (hne rfl)

/-- If the non-isolated part of `H` is a matching, then `H` embeds into a
canonical matching with one available edge for each vertex of `H`.  Isolated
vertices use their own private edge, while each non-isolated edge uses the
smaller of the two endpoint labels as its edge index. -/
theorem embeds_into_large_matchingGraph_of_isMatching_deleteIsolated
    {α : Type u} [Fintype α] (H : SimpleGraph α)
    (hmatch : IsMatchingGraph (deleteIsolated H)) :
    EmbedsAsSubgraph H (matchingGraph (Fintype.card α)) := by
  classical
  let enc : α ≃ Fin (Fintype.card α) := Fintype.equivFin α
  have support_left {x y : α} (hxy : H.Adj x y) : x ∈ H.support := by
    rw [SimpleGraph.mem_support]
    exact ⟨y, hxy⟩
  have support_right {x y : α} (hxy : H.Adj x y) : y ∈ H.support := by
    rw [SimpleGraph.mem_support]
    exact ⟨x, hxy.symm⟩
  have unique_of_two_adj {x y z : α} (hxy : H.Adj x y) (hxz : H.Adj x z) :
      y = z := by
    have hx : x ∈ H.support := support_left hxy
    have hy : y ∈ H.support := support_right hxy
    have hz : z ∈ H.support := support_right hxz
    have hxy' : (deleteIsolated H).Adj ⟨x, hx⟩ ⟨y, hy⟩ := by
      simpa [deleteIsolated] using hxy
    have hxz' : (deleteIsolated H).Adj ⟨x, hx⟩ ⟨z, hz⟩ := by
      simpa [deleteIsolated] using hxz
    exact congrArg Subtype.val (hmatch hxy' hxz')
  let mate (x : α) (hx : x ∈ H.support) : α :=
    Classical.choose (by
      rw [SimpleGraph.mem_support] at hx
      exact hx)
  have mate_adj (x : α) (hx : x ∈ H.support) : H.Adj x (mate x hx) := by
    dsimp [mate]
    exact Classical.choose_spec (by
      rw [SimpleGraph.mem_support] at hx
      exact hx)
  have mate_mem (x : α) (hx : x ∈ H.support) : mate x hx ∈ H.support := by
    rw [SimpleGraph.mem_support]
    exact ⟨x, (mate_adj x hx).symm⟩
  have mate_eq_of_adj {x y : α} (hxy : H.Adj x y) (hx : x ∈ H.support) :
      mate x hx = y := by
    exact unique_of_two_adj (mate_adj x hx) hxy
  let idx : α → Fin (Fintype.card α) := fun x =>
    if hx : x ∈ H.support then min (enc x) (enc (mate x hx)) else enc x
  let side : α → Bool := fun x =>
    if hx : x ∈ H.support then decide (enc (mate x hx) < enc x) else false
  let f : α → Fin (Fintype.card α) × Bool := fun x => (idx x, side x)
  refine ⟨f, ?_, ?_⟩
  · intro x y hxy
    have hidx : idx x = idx y := congrArg Prod.fst hxy
    have hside : side x = side y := congrArg Prod.snd hxy
    by_cases hx : x ∈ H.support
    · by_cases hy : y ∈ H.support
      · let mx := mate x hx
        let my := mate y hy
        by_cases hxlt : enc mx < enc x
        · have hylt : enc my < enc y := by
            by_contra hylt
            have hbad : side x ≠ side y := by
              simp [side, hx, hy, mx, my, hxlt, hylt]
            exact hbad hside
          have hmin : enc mx = enc my := by
            simpa [idx, hx, hy, mx, my, hxlt, hylt,
              min_eq_right (le_of_lt hxlt), min_eq_right (le_of_lt hylt)] using hidx
          have hmxmy : mx = my := enc.injective hmin
          have h1 : H.Adj mx x := by
            exact (mate_adj x hx).symm
          have h2 : H.Adj mx y := by
            simpa [mx, my, hmxmy] using (mate_adj y hy).symm
          exact unique_of_two_adj h1 h2
        · have hylt : ¬ enc my < enc y := by
            by_contra hylt
            have hbad : side x ≠ side y := by
              simp [side, hx, hy, mx, my, hxlt, hylt]
            exact hbad hside
          have hxle : enc x ≤ enc mx := le_of_not_gt hxlt
          have hyle : enc y ≤ enc my := le_of_not_gt hylt
          have hmin : enc x = enc y := by
            simpa [idx, hx, hy, mx, my, hxlt, hylt,
              min_eq_left hxle, min_eq_left hyle] using hidx
          exact enc.injective hmin
      · by_cases hxlt : enc (mate x hx) < enc x
        · have hmin : enc (mate x hx) = enc y := by
            simpa [idx, hx, hy, hxlt, min_eq_right (le_of_lt hxlt)] using hidx
          have hmate : mate x hx = y := enc.injective hmin
          exact False.elim (hy (by simpa [hmate] using mate_mem x hx))
        · have hxle : enc x ≤ enc (mate x hx) := le_of_not_gt hxlt
          have hmin : enc x = enc y := by
            simpa [idx, hx, hy, hxlt, min_eq_left hxle] using hidx
          have hxy' : x = y := enc.injective hmin
          exact False.elim (hy (by simpa [hxy'] using hx))
    · by_cases hy : y ∈ H.support
      · by_cases hylt : enc (mate y hy) < enc y
        · have hmin : enc x = enc (mate y hy) := by
            simpa [idx, hx, hy, hylt, min_eq_right (le_of_lt hylt)] using hidx
          have hmate : x = mate y hy := enc.injective hmin
          exact False.elim (hx (by simpa [hmate] using mate_mem y hy))
        · have hyle : enc y ≤ enc (mate y hy) := le_of_not_gt hylt
          have hmin : enc x = enc y := by
            simpa [idx, hx, hy, hylt, min_eq_left hyle] using hidx
          exact enc.injective hmin
      · have hmin : enc x = enc y := by
          simpa [idx, hx, hy] using hidx
        exact enc.injective hmin
  · intro x y hxy
    have hx : x ∈ H.support := support_left hxy
    have hy : y ∈ H.support := support_right hxy
    have hmx : mate x hx = y := mate_eq_of_adj hxy hx
    have hmy : mate y hy = x := mate_eq_of_adj hxy.symm hy
    change idx x = idx y ∧ side x ≠ side y
    constructor
    · simp [idx, hx, hy, hmx, hmy, min_comm]
    · have hne : enc x ≠ enc y := by
        intro h
        exact hxy.ne (enc.injective h)
      by_cases hlt : enc x < enc y
      · have hyx : ¬ enc y < enc x := not_lt_of_gt hlt
        simp [side, hx, hy, hmx, hmy, hlt, hyx]
      · have hyx : enc y < enc x := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hne)
        simp [side, hx, hy, hmx, hmy, hlt, hyx]

/-- A version of `matching_embedding_of_card_ge` whose size hypothesis is
phrased using the finite edge set of the coerced matching graph. -/
theorem matching_embedding_of_edgeFinset_card_ge
    {V : Type u} {G : SimpleGraph V}
    (M : G.Subgraph) (hM : M.IsMatching) [DecidableRel M.Adj] [Fintype M.verts]
    {b : ℕ} (hcard : b ≤ M.coe.edgeFinset.card) :
    EmbedsAsSubgraph (matchingGraph b) G := by
  classical
  have hcard' : Fintype.card (Fin b) ≤ Fintype.card M.coe.edgeSet := by
    simpa [SimpleGraph.edgeFinset_card] using hcard
  rcases Function.Embedding.nonempty_of_card_le hcard' with
    ⟨edgeEmb : Fin b ↪ M.coe.edgeSet⟩
  let left : Fin b → M.verts := fun i => (edgeEmb i).val.out.1
  let right : Fin b → M.verts := fun i => (edgeEmb i).val.out.2
  have edge_pair_eq (i : Fin b) :
      s(left i, right i) = (edgeEmb i).val := by
    change s((edgeEmb i).val.out.1, (edgeEmb i).val.out.2) = (edgeEmb i).val
    rw [Sym2.mk, (edgeEmb i).val.out_eq]
  have edge_adj_coe (i : Fin b) : M.coe.Adj (left i) (right i) := by
    change s(left i, right i) ∈ M.coe.edgeSet
    rw [edge_pair_eq i]
    exact (edgeEmb i).property
  have edge_adj_M (i : Fin b) : M.Adj (left i : V) (right i : V) :=
    edge_adj_coe i
  let endpoint : Fin b → Bool → M.verts := fun i side =>
    if side then right i else left i
  have selected_endpoint (i : Fin b) (side : Bool) :
      hM.toEdge (endpoint i side) =
        ⟨s((left i : V), (right i : V)), edge_adj_M i⟩ := by
    cases side
    · change hM.toEdge (left i) =
        ⟨s((left i : V), (right i : V)), edge_adj_M i⟩
      exact hM.toEdge_eq_of_adj (M.edge_vert (edge_adj_M i)) (edge_adj_M i)
    · change hM.toEdge (right i) =
        ⟨s((left i : V), (right i : V)), edge_adj_M i⟩
      calc
        hM.toEdge (right i) =
            ⟨s((right i : V), (left i : V)), (edge_adj_M i).symm⟩ :=
          hM.toEdge_eq_of_adj
            (M.edge_vert (edge_adj_M i).symm) (edge_adj_M i).symm
        _ = ⟨s((left i : V), (right i : V)), edge_adj_M i⟩ := by
          apply Subtype.ext
          exact Sym2.eq_swap
  have edge_eq_of_endpoint_eq
      {i j : Fin b} {si sj : Bool}
      (h : (endpoint i si : V) = (endpoint j sj : V)) :
      edgeEmb i = edgeEmb j := by
    have hto :
        hM.toEdge (endpoint i si) = hM.toEdge (endpoint j sj) := by
      exact congrArg hM.toEdge (Subtype.ext h)
    have hsymV :
        s((left i : V), (right i : V)) =
          s((left j : V), (right j : V)) := by
      have hto' :
          (⟨s((left i : V), (right i : V)), edge_adj_M i⟩ : M.edgeSet) =
            ⟨s((left j : V), (right j : V)), edge_adj_M j⟩ := by
        calc
          (⟨s((left i : V), (right i : V)), edge_adj_M i⟩ : M.edgeSet) =
              hM.toEdge (endpoint i si) := (selected_endpoint i si).symm
          _ = hM.toEdge (endpoint j sj) := hto
          _ = ⟨s((left j : V), (right j : V)), edge_adj_M j⟩ :=
              selected_endpoint j sj
      exact congrArg Subtype.val hto'
    have hmap_i :
        Sym2.map (fun x : M.verts => (x : V)) (edgeEmb i).val =
          s((left i : V), (right i : V)) := by
      rw [← edge_pair_eq i]
      rfl
    have hmap_j :
        Sym2.map (fun x : M.verts => (x : V)) (edgeEmb j).val =
          s((left j : V), (right j : V)) := by
      rw [← edge_pair_eq j]
      rfl
    have hmap :
        Sym2.map (fun x : M.verts => (x : V)) (edgeEmb i).val =
          Sym2.map (fun x : M.verts => (x : V)) (edgeEmb j).val := by
      calc
        Sym2.map (fun x : M.verts => (x : V)) (edgeEmb i).val =
            s((left i : V), (right i : V)) := hmap_i
        _ = s((left j : V), (right j : V)) := hsymV
        _ = Sym2.map (fun x : M.verts => (x : V)) (edgeEmb j).val := hmap_j.symm
    apply Subtype.ext
    exact (Sym2.map.injective (fun _ _ h => Subtype.ext h)) hmap
  let f : Fin b × Bool → V := fun p => endpoint p.1 p.2
  refine ⟨f, ?_, ?_⟩
  · intro p q hpq
    rcases p with ⟨i, si⟩
    rcases q with ⟨j, sj⟩
    change (endpoint i si : V) = (endpoint j sj : V) at hpq
    have hedge : edgeEmb i = edgeEmb j :=
      edge_eq_of_endpoint_eq hpq
    have hij : i = j := edgeEmb.injective hedge
    subst j
    cases si <;> cases sj
    · rfl
    · exfalso
      have hbad : (left i : V) = (right i : V) := by
        simpa [endpoint] using hpq
      exact (edge_adj_M i).ne hbad
    · exfalso
      have hbad : (right i : V) = (left i : V) := by
        simpa [endpoint] using hpq
      exact (edge_adj_M i).ne hbad.symm
    · rfl
  · intro p q hpq
    rcases p with ⟨i, si⟩
    rcases q with ⟨j, sj⟩
    rcases hpq with ⟨hij, hne⟩
    have hij' : i = j := by
      simpa using hij
    subst j
    cases si <;> cases sj
    · exact False.elim (hne rfl)
    · simpa [f, endpoint] using M.adj_sub (edge_adj_M i)
    · simpa [f, endpoint] using (M.adj_sub (edge_adj_M i)).symm
    · exact False.elim (hne rfl)

/--
Single-forbidden-graph lemma: `ex(n; H) = Θ(n)` iff the non-isolated part of
`H` is a forest with at least two edges.
-/
axiom singleForbiddenGraphLemma (H : FiniteSimpleGraph.{u}) :
    IsThetaLinear (fun n : ℕ => H.extremal n) →
      H.atLeastTwoEdgesAfterDeletingIsolated

/--
If every edge of a finite graph meets a finite vertex set `T`, and every vertex
of `T` has degree at most `A`, then the number of edges is at most `#T * A`.

This is the counting core of the star/matching obstruction: take `T` to be the
vertices saturated by a maximal matching.
-/
theorem edgeCount_le_card_mul_degree_bound_of_edges_meet_finset
    {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset V) (A : ℕ)
    (hdeg : ∀ v ∈ T, G.degree v ≤ A)
    (hcover : ∀ ⦃x y : V⦄, G.Adj x y → x ∈ T ∨ y ∈ T) :
    edgeCount G ≤ T.card * A := by
  classical
  have hedge : edgeCount G = G.edgeFinset.card := by
    rw [edgeCount, Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
  have h_edges_subset :
      G.edgeFinset ⊆ T.biUnion (fun v => G.incidenceFinset v) := by
    intro e he
    induction e using Sym2.ind with
    | h x y =>
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
        rw [Finset.mem_biUnion]
        rcases hcover he with hx | hy
        · refine ⟨x, hx, ?_⟩
          rw [SimpleGraph.mem_incidenceFinset]
          exact (G.mk'_mem_incidenceSet_left_iff).2 he
        · refine ⟨y, hy, ?_⟩
          rw [SimpleGraph.mem_incidenceFinset]
          exact (G.mk'_mem_incidenceSet_right_iff).2 he
  rw [hedge]
  refine (Finset.card_le_card h_edges_subset).trans ?_
  refine Finset.card_biUnion_le_card_mul T (fun v => G.incidenceFinset v) A ?_
  intro v hv
  simpa [SimpleGraph.card_incidenceFinset_eq_degree] using hdeg v hv

/--
The concrete upper bound used in the \(O(1)\) case.  If a graph has maximum
degree at most `a - 1`, and all edges meet a set of at most `2 * (b - 1)`
vertices, then it has at most `2 * (b - 1) * (a - 1)` edges.
-/
theorem edgeCount_le_two_mul_pred_mul_pred_of_maxDegree_and_edgeCover
    {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (a b : ℕ) (T : Finset V)
    (hmax : G.maxDegree ≤ a - 1)
    (hTcard : T.card ≤ 2 * (b - 1))
    (hcover : ∀ ⦃x y : V⦄, G.Adj x y → x ∈ T ∨ y ∈ T) :
    edgeCount G ≤ 2 * (b - 1) * (a - 1) := by
  classical
  have hdeg : ∀ v ∈ T, G.degree v ≤ a - 1 := by
    intro v _hv
    exact (G.degree_le_maxDegree v).trans hmax
  exact
    (edgeCount_le_card_mul_degree_bound_of_edges_meet_finset
      G T (a - 1) hdeg hcover).trans
      (Nat.mul_le_mul_right (a - 1) hTcard)

/-- A host graph avoids every member of a finite indexed family. -/
def FamilyFree {ι : Type v}
    (F : ι → FiniteSimpleGraph.{u})
    {W : Type w}
    (G : SimpleGraph W) : Prop :=
  ∀ i : ι, IsHFree (F i).graph G

/-- The extremal number for a finite indexed family of forbidden graphs. -/
def extremalFamily {ι : Type v} [Finite ι]
    (F : ι → FiniteSimpleGraph.{u}) (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ G : SimpleGraph (Fin n), FamilyFree F G ∧ edgeCount G = m}

/-- A family-free graph is, in particular, free of each chosen member of the
family, so the family extremal number is bounded above by each individual
extremal number. -/
theorem extremalFamily_le_extremal
    {ι : Type v} [Finite ι]
    (F : ι → FiniteSimpleGraph.{u}) (i : ι) :
    ∀ n, extremalFamily F n ≤ (F i).extremal n := by
  intro n
  unfold extremalFamily
  change sSup {m : ℕ |
      ∃ G : SimpleGraph (Fin n), FamilyFree F G ∧ edgeCount G = m} ≤
    extremalNumber (F i).graph n
  refine nat_sSup_le_of_forall_le ?_
  intro m hm
  rcases hm with ⟨G, hfree, rfl⟩
  exact extremalNumber_ge_of_host (F i).graph G (hfree i)

/-- The family extremal number is `O(n)` as soon as one member has linear
single-forbidden extremal number. -/
theorem extremalFamily_isOLinear_of_member
    {ι : Type v} [Finite ι]
    (F : ι → FiniteSimpleGraph.{u}) (i : ι)
    (hi : IsThetaLinear (fun n : ℕ => (F i).extremal n)) :
    IsOLinear (fun n : ℕ => extremalFamily F n) := by
  unfold IsOLinear
  have hToSingle :
      (fun n : ℕ => (extremalFamily F n : ℝ)) =O[atTop]
        (fun n : ℕ => ((F i).extremal n : ℝ)) := by
    refine IsBigO.of_bound (1 : ℝ) (Filter.Eventually.of_forall ?_)
    intro n
    have hreal :
        (extremalFamily F n : ℝ) ≤ ((F i).extremal n : ℝ) := by
      exact_mod_cast extremalFamily_le_extremal F i n
    simpa using hreal
  have hi' := hi
  unfold IsThetaLinear at hi'
  exact hToSingle.trans hi'.1

/--
If every admissible `n`-vertex host graph has at most `C` edges, then the
`sSup`-defined extremal value is also at most `C`.
-/
theorem extremalFamily_le_of_forall_edgeCount_le
    {ι : Type v} [Finite ι]
    (F : ι → FiniteSimpleGraph.{u}) (C : ℕ)
    (hC : ∀ n (G : SimpleGraph (Fin n)), FamilyFree F G → edgeCount G ≤ C) :
    ∀ n, extremalFamily F n ≤ C := by
  intro n
  unfold extremalFamily
  refine nat_sSup_le_of_forall_le ?_
  intro m hm
  rcases hm with ⟨G, hfree, rfl⟩
  exact hC n G hfree

/-- Any admissible host contributes a lower bound to the family extremal
number. -/
theorem extremalFamily_ge_of_host
    {ι : Type v} [Finite ι]
    (F : ι → FiniteSimpleGraph.{u}) {n : ℕ}
    (G : SimpleGraph (Fin n))
    (hfree : FamilyFree F G) :
    edgeCount G ≤ extremalFamily F n := by
  unfold extremalFamily
  refine nat_le_sSup_of_mem_of_forall_le (C := n.choose 2) ?_ ?_
  · exact ⟨G, hfree, rfl⟩
  · intro m hm
    rcases hm with ⟨G', _hfree, rfl⟩
    exact edgeCount_le_complete_bound G'

/-- The family contains both a star and a matching, each with at least two edges
after deleting isolated vertices. -/
def FamilyContainsStarMatchingPair {ι : Type v}
    (F : ι → FiniteSimpleGraph.{u}) : Prop :=
  (∃ i : ι, (F i).starWithAtLeastTwoEdgesAfterDeletingIsolated) ∧
    (∃ j : ι, (F j).matchingWithAtLeastTwoEdgesAfterDeletingIsolated)

/-- An embedding sends every non-isolated edge of the source injectively into
an edge of the target. -/
theorem edgeCount_deleteIsolated_le_of_embeds
    {α : Type u} {β : Type v}
    (H : SimpleGraph α) (G : SimpleGraph β)
    [Finite G.edgeSet]
    (hemb : EmbedsAsSubgraph H G) :
    edgeCount (deleteIsolated H) ≤ edgeCount G := by
  rcases hemb with ⟨f, hf, hmap⟩
  let g : H.support → β := fun x => f (x : α)
  let edgeMap : (deleteIsolated H).edgeSet → G.edgeSet := fun e =>
    ⟨Sym2.map g e.1, by
      rcases e with ⟨e, he⟩
      change Sym2.map g e ∈ G.edgeSet
      induction e using Sym2.inductionOn with
      | _ x y =>
          change s(g x, g y) ∈ G.edgeSet
          rw [SimpleGraph.mem_edgeSet]
          have hxy : (deleteIsolated H).Adj x y := by
            simpa [SimpleGraph.mem_edgeSet] using he
          exact hmap (by simpa [deleteIsolated, g] using hxy)⟩
  have h_edgeMap_injective : Function.Injective edgeMap := by
    intro e₁ e₂ h
    apply Subtype.ext
    have hcoe :
        Sym2.map g e₁.1 = Sym2.map g e₂.1 := by
      exact congrArg Subtype.val h
    have hvertex : Function.Injective g := by
      intro x y hxy
      change f (x : α) = f (y : α) at hxy
      exact Subtype.ext (hf hxy)
    exact (Sym2.map.injective hvertex) hcoe
  exact Nat.card_le_card_of_injective edgeMap h_edgeMap_injective

/-- No graph whose non-isolated part has at least two edges embeds into a
host with at most one edge. -/
theorem isHFree_of_two_deleteIsolated_edges_of_edgeCount_le_one
    {α : Type u} {β : Type v}
    (H : SimpleGraph α) (G : SimpleGraph β)
    [Finite G.edgeSet]
    (hTwo : 2 ≤ edgeCount (deleteIsolated H))
    (hG : edgeCount G ≤ 1) :
    IsHFree H G := by
  intro hemb
  have hle : edgeCount (deleteIsolated H) ≤ edgeCount G :=
    edgeCount_deleteIsolated_le_of_embeds H G hemb
  omega

/-- The labelled graph on `Fin n` with exactly the edge joining `0` and `1`.
The hypothesis `2 ≤ n` supplies the two distinct vertices. -/
def oneEdgeHost (n : ℕ) (hn : 2 ≤ n) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet
    ({s((⟨0, by omega⟩ : Fin n), (⟨1, by omega⟩ : Fin n))} :
      Set (Sym2 (Fin n)))

/-- The one-edge host has exactly one edge. -/
theorem edgeCount_oneEdgeHost {n : ℕ} (hn : 2 ≤ n) :
    edgeCount (oneEdgeHost n hn) = 1 := by
  let u : Fin n := ⟨0, by omega⟩
  let v : Fin n := ⟨1, by omega⟩
  have huv : u ≠ v := by
    intro h
    have : (0 : ℕ) = 1 := congrArg Fin.val h
    omega
  unfold oneEdgeHost edgeCount
  change Nat.card (SimpleGraph.edgeSet
    (SimpleGraph.fromEdgeSet ({s(u, v)} : Set (Sym2 (Fin n))))) = 1
  rw [SimpleGraph.edgeSet_fromEdgeSet]
  have hset :
      ({s(u, v)} : Set (Sym2 (Fin n))) \ Sym2.diagSet = {s(u, v)} := by
    ext e
    by_cases he : e = s(u, v)
    · subst he
      simp [Sym2.mk_isDiag_iff, huv]
    · simp [he]
  rw [hset]
  simp

/-- Single-edge lower-bound construction: if every forbidden graph has at
least two non-isolated edges, then the one-edge host is admissible for all large
`n`, so the family extremal function is eventually at least one. -/
theorem oneEdgeConstruction_extremalFamily_eventually_one_le
    {ι : Type v} [Finite ι] [Nonempty ι]
    (F : ι → FiniteSimpleGraph.{u})
    (hTwo : ∀ i : ι, (F i).atLeastTwoEdgesAfterDeletingIsolated) :
    ∀ᶠ n in atTop, 1 ≤ extremalFamily F n := by
  refine eventually_atTop.2 ⟨2, ?_⟩
  intro n hn
  let G : SimpleGraph (Fin n) := oneEdgeHost n hn
  have hfree : FamilyFree F G := by
    intro i
    classical
    letI : Finite G.edgeSet := inferInstance
    exact isHFree_of_two_deleteIsolated_edges_of_edgeCount_le_one
      (F i).graph G (hTwo i) (by
        rw [edgeCount_oneEdgeHost hn])
  have hhost : edgeCount G ≤ extremalFamily F n :=
    extremalFamily_ge_of_host F G hfree
  have hone : edgeCount G = 1 := edgeCount_oneEdgeHost hn
  omega

/-- A positive edge count produces an adjacent pair. -/
theorem exists_adj_of_edgeCount_pos
    {V : Type u} (G : SimpleGraph V) [Finite G.edgeSet]
    (hpos : 0 < edgeCount G) :
    ∃ x y : V, G.Adj x y := by
  classical
  letI : Fintype G.edgeSet := Fintype.ofFinite G.edgeSet
  rw [edgeCount, Nat.card_eq_fintype_card] at hpos
  rcases Fintype.card_pos_iff.mp hpos with ⟨e⟩
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ x y =>
      have hxy : G.Adj x y := by
        simpa [SimpleGraph.mem_edgeSet] using he
      exact ⟨x, y, hxy⟩

/-- The labelled star on `Fin n`, centered at `0`, has exactly `n - 1` edges. -/
theorem edgeCount_starGraph_fin {n : ℕ} (hn : 1 ≤ n) :
    edgeCount (starGraph (⟨0, by omega⟩ : Fin n)) = n - 1 := by
  classical
  let c : Fin n := ⟨0, by omega⟩
  let G : SimpleGraph (Fin n) := starGraph c
  have hedge : edgeCount G = G.edgeFinset.card := by
    rw [edgeCount, Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
  have hinc : G.edgeFinset = G.incidenceFinset c := by
    ext e
    induction e using Sym2.inductionOn with
    | _ x y =>
        simp only [G, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_incidenceFinset,
          SimpleGraph.mk'_mem_incidenceSet_iff, SimpleGraph.mem_edgeSet, starGraph]
        constructor
        · intro hxy
          refine ⟨hxy, ?_⟩
          rcases hxy with hxy | hxy
          · exact Or.inl hxy.1.symm
          · exact Or.inr hxy.1.symm
        · intro hxy
          exact hxy.1
  have hneighbors : G.neighborFinset c = Finset.univ.erase c := by
    ext v
    simp [G, SimpleGraph.mem_neighborFinset, starGraph]
  calc
    edgeCount G = G.edgeFinset.card := hedge
    _ = (G.incidenceFinset c).card := by rw [hinc]
    _ = G.degree c := SimpleGraph.card_incidenceFinset_eq_degree G c
    _ = (G.neighborFinset c).card := (SimpleGraph.card_neighborFinset_eq_degree G c).symm
    _ = (Finset.univ.erase c).card := by rw [hneighbors]
    _ = n - 1 := by simp

/-- If a graph with at least one edge embeds into a star, then its reduced
non-isolated graph is a star. -/
theorem deleteIsolated_isStar_of_embeds_into_star
    {α : Type u} {β : Type v}
    {H : SimpleGraph α} {c : β}
    (hemb : EmbedsAsSubgraph H (starGraph c))
    (hne : ∃ x y : α, H.Adj x y) :
    IsStar (deleteIsolated H) := by
  rcases hemb with ⟨f, hf, hmap⟩
  rcases hne with ⟨x₀, y₀, hxy₀⟩
  have hstar₀ : (starGraph c).Adj (f x₀) (f y₀) := hmap hxy₀
  have hcenter_exists : ∃ z : α, z ∈ H.support ∧ f z = c := by
    rcases hstar₀ with h | h
    · exact ⟨x₀, ⟨y₀, hxy₀⟩, h.1⟩
    · exact ⟨y₀, ⟨x₀, hxy₀.symm⟩, h.1⟩
  rcases hcenter_exists with ⟨z, hz_support, hfz⟩
  let center : H.support := ⟨z, hz_support⟩
  have eq_center_of_image_eq
      (u : H.support) (hu : f (u : α) = c) :
      u = center := by
    apply Subtype.ext
    exact hf (hu.trans hfz.symm)
  have image_ne_center_of_ne
      (u : H.support) (hu : u ≠ center) :
      f (u : α) ≠ c := by
    intro hfu
    exact hu (eq_center_of_image_eq u hfu)
  have adj_center_of_ne_center
      (u : H.support) (hu : u ≠ center) :
      H.Adj center.1 u.1 := by
    rcases u.2 with ⟨w, huw⟩
    have hstar : (starGraph c).Adj (f (u : α)) (f w) := hmap huw
    rcases hstar with h | h
    · exact False.elim ((image_ne_center_of_ne u hu) h.1)
    · have hw_eq : w = center.1 := by
        exact hf (h.1.trans hfz.symm)
      have huw' : H.Adj u.1 center.1 := by
        simpa [hw_eq] using huw
      exact huw'.symm
  refine ⟨center, ?_⟩
  ext u v
  constructor
  · intro huv
    have hH : H.Adj u.1 v.1 := by
      simpa [deleteIsolated] using huv
    have hstar : (starGraph c).Adj (f (u : α)) (f (v : α)) := hmap hH
    rcases hstar with h | h
    · have hu : u = center := eq_center_of_image_eq u h.1
      exact Or.inl ⟨hu, by
        intro hv
        exact huv.ne (hu.trans hv.symm)⟩
    · have hv : v = center := eq_center_of_image_eq v h.1
      exact Or.inr ⟨hv, by
        intro hu
        exact huv.ne (hu.trans hv.symm)⟩
  · intro huv
    rcases huv with h | h
    · rcases h with ⟨hu, hv_ne⟩
      subst hu
      have hcv : H.Adj center.1 v.1 :=
        adj_center_of_ne_center v hv_ne
      simpa [deleteIsolated] using hcv
    · rcases h with ⟨hv, hu_ne⟩
      subst hv
      have hcu : H.Adj center.1 u.1 :=
        adj_center_of_ne_center u hu_ne
      simpa [deleteIsolated] using hcu.symm

/-- Star lower-bound construction: if no forbidden member reduces to a star,
then the `n`-vertex star is family-free and has `n - 1` edges. -/
theorem starConstruction_extremalFamily_eventually_pred_le
    {ι : Type v} [Finite ι] [Nonempty ι]
    (F : ι → FiniteSimpleGraph.{u})
    (hTwo : ∀ i : ι, (F i).atLeastTwoEdgesAfterDeletingIsolated)
    (hNoStar : ∀ i : ι, ¬ (F i).starAfterDeletingIsolated) :
    ∀ᶠ n in atTop, n - 1 ≤ extremalFamily F n := by
  refine eventually_atTop.2 ⟨1, ?_⟩
  intro n hn
  classical
  have hnpos : 0 < n := Nat.succ_le_iff.mp hn
  let c : Fin n := ⟨0, hnpos⟩
  let G : SimpleGraph (Fin n) := starGraph c
  have hfree : FamilyFree F G := by
    intro i hemb
    have hpos : 0 < edgeCount (deleteIsolated (F i).graph) := by
      have htwo_i : 2 ≤ edgeCount (deleteIsolated (F i).graph) := hTwo i
      omega
    rcases exists_adj_of_edgeCount_pos (deleteIsolated (F i).graph) hpos with
      ⟨x, y, hxy⟩
    have hraw : ∃ x y : (F i).V, (F i).graph.Adj x y := by
      exact ⟨x.1, y.1, by simpa [deleteIsolated] using hxy⟩
    exact hNoStar i
      (deleteIsolated_isStar_of_embeds_into_star
        (H := (F i).graph) (c := c) hemb hraw)
  have hhost : edgeCount G ≤ extremalFamily F n :=
    extremalFamily_ge_of_host F G hfree
  have hcount : edgeCount G = n - 1 := by
    simpa [G, c] using edgeCount_starGraph_fin (n := n) hn
  omega

/-- Left endpoint of the `k`th edge in the labelled matching host on `Fin n`. -/
def matchingHostLeft (n : ℕ) (k : Fin (n / 2)) : Fin n :=
  ⟨2 * k.val, by have hk := k.isLt; omega⟩

/-- Right endpoint of the `k`th edge in the labelled matching host on `Fin n`. -/
def matchingHostRight (n : ℕ) (k : Fin (n / 2)) : Fin n :=
  ⟨2 * k.val + 1, by have hk := k.isLt; omega⟩

theorem matchingHost_left_ne_right (n : ℕ) (k : Fin (n / 2)) :
    matchingHostLeft n k ≠ matchingHostRight n k := by
  intro h
  have hv := congrArg Fin.val h
  simp [matchingHostLeft, matchingHostRight] at hv

/-- The labelled `n`-vertex host consisting of the disjoint edges
`{0,1}, {2,3}, ...`, with one isolated vertex left over when `n` is odd. -/
def matchingHost (n : ℕ) : SimpleGraph (Fin n) where
  Adj x y := ∃ k : Fin (n / 2),
    (x = matchingHostLeft n k ∧ y = matchingHostRight n k) ∨
      (x = matchingHostRight n k ∧ y = matchingHostLeft n k)
  symm := by
    intro x y h
    rcases h with ⟨k, h | h⟩
    · exact ⟨k, Or.inr ⟨h.2, h.1⟩⟩
    · exact ⟨k, Or.inl ⟨h.2, h.1⟩⟩
  loopless := by
    constructor
    intro x h
    rcases h with ⟨k, h | h⟩
    · exact matchingHost_left_ne_right n k (h.1.symm.trans h.2)
    · exact matchingHost_left_ne_right n k (h.2.symm.trans h.1)

/-- The labelled matching host is a matching graph. -/
theorem matchingHost_isMatchingGraph (n : ℕ) :
    IsMatchingGraph (matchingHost n) := by
  intro x y z hxy hxz
  rcases hxy with ⟨k, hxy | hxy⟩
  · rcases hxy with ⟨hxk, hyk⟩
    rcases hxz with ⟨l, hxz | hxz⟩
    · rcases hxz with ⟨hxl, hzl⟩
      subst y
      subst z
      have hkl : k = l := by
        apply Fin.ext
        have hv := congrArg Fin.val (hxk.symm.trans hxl)
        simp [matchingHostLeft] at hv
        omega
      subst l
      rfl
    · rcases hxz with ⟨hzl, hxl⟩
      have hbad := congrArg Fin.val (hxk.symm.trans hzl)
      simp [matchingHostLeft, matchingHostRight] at hbad
      omega
  · rcases hxy with ⟨hyk, hxk⟩
    rcases hxz with ⟨l, hxz | hxz⟩
    · rcases hxz with ⟨hxl, hzl⟩
      have hbad := congrArg Fin.val (hyk.symm.trans hxl)
      simp [matchingHostLeft, matchingHostRight] at hbad
      omega
    · rcases hxz with ⟨hzl, hxl⟩
      subst y
      subst z
      have hkl : k = l := by
        apply Fin.ext
        have hv := congrArg Fin.val (hyk.symm.trans hzl)
        simp [matchingHostRight] at hv
        omega
      subst l
      rfl

/-- The unordered edge corresponding to the `k`th pair of the matching host. -/
def matchingHostEdge (n : ℕ) (k : Fin (n / 2)) : Sym2 (Fin n) :=
  s(matchingHostLeft n k, matchingHostRight n k)

/-- The matching host on `Fin n` has exactly `⌊n/2⌋` edges. -/
theorem edgeCount_matchingHost (n : ℕ) :
    edgeCount (matchingHost n) = n / 2 := by
  classical
  let G : SimpleGraph (Fin n) := matchingHost n
  let edgeEmb : Fin (n / 2) → G.edgeSet := fun k =>
    ⟨matchingHostEdge n k, by
      rw [matchingHostEdge, SimpleGraph.mem_edgeSet]
      exact ⟨k, Or.inl ⟨rfl, rfl⟩⟩⟩
  have hinj : Function.Injective edgeEmb := by
    intro k l h
    apply Fin.ext
    have hs : matchingHostEdge n k = matchingHostEdge n l :=
      congrArg Subtype.val h
    rw [matchingHostEdge, matchingHostEdge, Sym2.eq, Sym2.rel_iff] at hs
    rcases hs with hs | hs
    · have hv := congrArg Fin.val hs.1
      simp [matchingHostLeft] at hv
      omega
    · have hv := congrArg Fin.val hs.1
      simp [matchingHostLeft, matchingHostRight] at hv
      omega
  have hsurj : Function.Surjective edgeEmb := by
    intro e
    rcases e with ⟨e, he⟩
    induction e using Sym2.inductionOn with
    | _ x y =>
        have hxy : G.Adj x y := by
          simpa [G, SimpleGraph.mem_edgeSet] using he
        rcases hxy with ⟨k, h | h⟩
        · refine ⟨k, ?_⟩
          apply Subtype.ext
          simp [edgeEmb, matchingHostEdge, h.1, h.2]
        · refine ⟨k, ?_⟩
          apply Subtype.ext
          calc
            matchingHostEdge n k =
                s(matchingHostRight n k, matchingHostLeft n k) := by
              simp [matchingHostEdge, Sym2.eq_swap]
            _ = s(x, y) := by simp [h.1, h.2]
  have hcard : Fintype.card (Fin (n / 2)) = Fintype.card G.edgeSet :=
    Fintype.card_of_bijective (f := edgeEmb) ⟨hinj, hsurj⟩
  rw [edgeCount, Nat.card_eq_fintype_card]
  simpa using hcard.symm

/-- If a graph embeds into a matching graph, then its non-isolated part is a
matching graph. -/
theorem deleteIsolated_isMatchingGraph_of_embeds_into_isMatchingGraph
    {α : Type u} {β : Type v}
    {H : SimpleGraph α} {G : SimpleGraph β}
    (hG : IsMatchingGraph G)
    (hemb : EmbedsAsSubgraph H G) :
    IsMatchingGraph (deleteIsolated H) := by
  rcases hemb with ⟨f, hf, hmap⟩
  intro x y z hxy hxz
  apply Subtype.ext
  apply hf
  exact hG (hmap (by simpa [deleteIsolated] using hxy))
    (hmap (by simpa [deleteIsolated] using hxz))

/-- Matching lower-bound construction: if no forbidden member reduces to a
matching, then a matching of size `⌊n/2⌋` is family-free on `n` vertices. -/
theorem matchingConstruction_extremalFamily_eventually_half_le
    {ι : Type v} [Finite ι] [Nonempty ι]
    (F : ι → FiniteSimpleGraph.{u})
    (_hTwo : ∀ i : ι, (F i).atLeastTwoEdgesAfterDeletingIsolated)
    (hNoMatching : ∀ i : ι, ¬ (F i).matchingAfterDeletingIsolated) :
    ∀ᶠ n in atTop, n / 2 ≤ extremalFamily F n := by
  refine eventually_atTop.2 ⟨0, ?_⟩
  intro n _hn
  let G : SimpleGraph (Fin n) := matchingHost n
  have hfree : FamilyFree F G := by
    intro i hemb
    exact hNoMatching i
      (deleteIsolated_isMatchingGraph_of_embeds_into_isMatchingGraph
        (matchingHost_isMatchingGraph n) hemb)
  have hhost : edgeCount G ≤ extremalFamily F n :=
    extremalFamily_ge_of_host F G hfree
  have hcount : edgeCount G = n / 2 := by
    simpa [G] using edgeCount_matchingHost n
  omega

/-- If the non-isolated part of `H` is a star and a target vertex has at least
`|V(H)|` neighbors, then `H` embeds into the target graph.  Isolated vertices
of `H` are harmless: they are sent injectively to unused neighbors, and only
edge preservation is required. -/
theorem embeds_of_deleteIsolated_isStar_of_degree_ge_card
    {α : Type u} {β : Type v} [Fintype α]
    (H : SimpleGraph α) (G : SimpleGraph β) (v : β)
    [Fintype (G.neighborSet v)]
    (hstar : IsStar (deleteIsolated H))
    (hdeg : Fintype.card α ≤ G.degree v) :
    EmbedsAsSubgraph H G := by
  classical
  rcases hstar with ⟨c, hc⟩
  let c0 : α := c
  have hcard : Fintype.card α ≤ Fintype.card (G.neighborSet v) := by
    simpa using hdeg
  rcases Function.Embedding.nonempty_of_card_le hcard with
    ⟨leaf : α ↪ G.neighborSet v⟩
  let f : α → β := fun x => if x = c0 then v else leaf x
  refine ⟨f, ?_, ?_⟩
  · intro x y hxy
    by_cases hx : x = c0
    · by_cases hy : y = c0
      · exact hx.trans hy.symm
      · exfalso
        have hv_leaf : v = (leaf y : β) := by
          simpa [f, hx, hy] using hxy
        exact (leaf y).property.ne hv_leaf
    · by_cases hy : y = c0
      · exfalso
        have hleaf_v : (leaf x : β) = v := by
          simpa [f, hx, hy] using hxy
        exact (leaf x).property.ne hleaf_v.symm
      · have hleaf : (leaf x : β) = (leaf y : β) := by
          simpa [f, hx, hy] using hxy
        exact leaf.injective (Subtype.ext hleaf)
  · intro x y hxy
    have hx_support : x ∈ H.support := by
      rw [SimpleGraph.mem_support]
      exact ⟨y, hxy⟩
    have hy_support : y ∈ H.support := by
      rw [SimpleGraph.mem_support]
      exact ⟨x, hxy.symm⟩
    let sx : H.support := ⟨x, hx_support⟩
    let sy : H.support := ⟨y, hy_support⟩
    have hred : (deleteIsolated H).Adj sx sy := by
      simpa [deleteIsolated, sx, sy] using hxy
    have hstar_adj : (starGraph c).Adj sx sy := by
      rw [hc] at hred
      exact hred
    rcases hstar_adj with hcenter | hcenter
    · have hx : x = c0 := by
        exact congrArg Subtype.val hcenter.1
      have hy : y ≠ c0 := by
        intro hy
        exact hcenter.2 (Subtype.ext hy)
      have hfx : f x = v := by
        simp [f, hx]
      have hfy : f y = (leaf y : β) := by
        simp [f, hy]
      rw [hfx, hfy]
      exact (leaf y).property
    · have hy : y = c0 := by
        exact congrArg Subtype.val hcenter.1
      have hx : x ≠ c0 := by
        intro hx
        exact hcenter.2 (Subtype.ext hx)
      have hfx : f x = (leaf x : β) := by
        simp [f, hx]
      have hfy : f y = v := by
        simp [f, hy]
      rw [hfx, hfy]
      exact ((leaf x).property).symm

/--
Degree-bound extraction from a forbidden star.  If `F i`, after deleting
isolated vertices, is a star, then an `F`-free host graph has maximum degree
bounded by the number of vertices of `F i`.

The proof is the direct pigeonhole embedding argument: if a host vertex had too
many neighbors, send the center of the reduced star to that vertex and inject
all other vertices of `F i` into distinct neighbors.
-/
theorem familyFree_maxDegree_le_pred_card_of_star
    {ι : Type v} [Finite ι] {F : ι → FiniteSimpleGraph.{u}}
    {i : ι}
    (hstar : (F i).starWithAtLeastTwoEdgesAfterDeletingIsolated)
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfree : FamilyFree F G) :
    G.maxDegree ≤ Fintype.card (F i).V - 1 := by
  classical
  refine G.maxDegree_le_of_forall_degree_le
    (Fintype.card (F i).V - 1) ?_
  intro v
  by_contra hnot
  have hdeg : Fintype.card (F i).V ≤ G.degree v := by
    omega
  exact hfree i
    (embeds_of_deleteIsolated_isStar_of_degree_ge_card
      (F i).graph G v hstar.1 hdeg)

/-- A maximal matching exists, and the vertices it saturates cover every edge. -/
theorem exists_maximalMatching_edgeCover
    {n : ℕ} (G : SimpleGraph (Fin n)) :
    ∃ M : G.Subgraph,
      M.IsMatching ∧
        Maximal (fun N : G.Subgraph => N.IsMatching) M ∧
          ∀ ⦃x y : Fin n⦄, G.Adj x y → x ∈ M.verts ∨ y ∈ M.verts := by
  classical
  have hbot : (⊥ : G.Subgraph).IsMatching := by
    intro v hv
    simp at hv
  rcases Finite.exists_le_maximal
      (α := G.Subgraph) (p := fun N : G.Subgraph => N.IsMatching) hbot with
    ⟨M, _hbot_le, hmax⟩
  refine ⟨M, hmax.1, hmax, ?_⟩
  intro x y hxy
  by_contra hnot
  push Not at hnot
  have hdisj : Disjoint M.support (G.subgraphOfAdj hxy).support := by
    rw [hmax.1.support_eq_verts, SimpleGraph.support_subgraphOfAdj]
    rw [Set.disjoint_left]
    intro z hz hzxy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hzxy
    rcases hzxy with rfl | rfl
    · exact hnot.1 hz
    · exact hnot.2 hz
  have hsup_match : (M ⊔ G.subgraphOfAdj hxy).IsMatching :=
    hmax.1.sup (SimpleGraph.Subgraph.IsMatching.subgraphOfAdj hxy) hdisj
  have hsup_le_M : M ⊔ G.subgraphOfAdj hxy ≤ M :=
    hmax.2 hsup_match le_sup_left
  have hedge_le_M : G.subgraphOfAdj hxy ≤ M :=
    le_trans le_sup_right hsup_le_M
  have hxM : x ∈ M.verts :=
    hedge_le_M.1 (by simp)
  exact hnot.1 hxM

/-- A matching saturates exactly twice as many vertices as it has edges. -/
theorem matching_verts_toFinset_card_eq_two_mul_edgeFinset_card
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (M : G.Subgraph) [DecidableRel M.Adj] [Fintype M.verts]
    (hM : M.IsMatching) :
    M.verts.toFinset.card = 2 * M.coe.edgeFinset.card := by
  classical
  rw [← M.coe.sum_degrees_eq_twice_card_edges]
  have hdeg_one :
      ∀ x : M.verts,
        @SimpleGraph.Subgraph.degree V G M (x : V) (SimpleGraph.Subgraph.finiteAt x) = 1 := by
    intro x
    rw [SimpleGraph.Subgraph.degree_eq_one_iff_existsUnique_adj]
    exact hM x.property
  simp [hdeg_one]

/--
Matching-bound extraction from a forbidden matching.  If `F j`, after deleting
isolated vertices, is a matching, then an `F`-free host graph has a vertex cover
of bounded size.

Combinatorially, take a maximal matching `M` in the host.  If an edge missed
`V(M)`, then `M` was not maximal.  If `V(M)` were too large, then the forbidden
matching member of the family would embed.
-/
theorem familyFree_exists_edgeCover_card_le_two_mul_pred_card_of_matching
    {ι : Type v} [Finite ι] {F : ι → FiniteSimpleGraph.{u}}
    {j : ι}
    (hmatching : (F j).matchingWithAtLeastTwoEdgesAfterDeletingIsolated)
    {n : ℕ} (G : SimpleGraph (Fin n))
    (hfree : FamilyFree F G) :
    ∃ T : Finset (Fin n),
      T.card ≤ 2 * (Fintype.card (F j).V - 1) ∧
        ∀ ⦃x y : Fin n⦄, G.Adj x y → x ∈ T ∨ y ∈ T := by
  classical
  rcases exists_maximalMatching_edgeCover G with ⟨M, hM, _hmax, hcover⟩
  letI : DecidableRel M.Adj := Classical.decRel _
  letI : Fintype M.verts := M.verts.toFinite.fintype
  let T : Finset (Fin n) := M.verts.toFinset
  refine ⟨T, ?_, ?_⟩
  · have hedge_lt : M.coe.edgeFinset.card < Fintype.card (F j).V := by
      by_contra hnot
      have hedge_ge : Fintype.card (F j).V ≤ M.coe.edgeFinset.card := by
        omega
      have hH_to_matching :
          EmbedsAsSubgraph (F j).graph (matchingGraph (Fintype.card (F j).V)) :=
        embeds_into_large_matchingGraph_of_isMatching_deleteIsolated
          (F j).graph hmatching.1
      have hmatching_to_G :
          EmbedsAsSubgraph (matchingGraph (Fintype.card (F j).V)) G :=
        matching_embedding_of_edgeFinset_card_ge M hM hedge_ge
      exact hfree j (hH_to_matching.trans hmatching_to_G)
    have hT :
        T.card = 2 * M.coe.edgeFinset.card := by
      simpa [T] using
        matching_verts_toFinset_card_eq_two_mul_edgeFinset_card M hM
    have hedge_le : M.coe.edgeFinset.card ≤ Fintype.card (F j).V - 1 := by
      omega
    calc
      T.card = 2 * M.coe.edgeFinset.card := hT
      _ ≤ 2 * (Fintype.card (F j).V - 1) :=
        Nat.mul_le_mul_left 2 hedge_le
  · intro x y hxy
    simpa [T] using hcover hxy

/--
Graph-theoretic bridge for the star/matching obstruction.  The proof extracts
the forbidden star and matching, converts them into a maximum-degree bound and a
bounded matching-number statement, chooses a maximal matching in the host graph,
and applies `edgeCount_le_two_mul_pred_mul_pred_of_maxDegree_and_edgeCover`.
-/
theorem familyFree_edgeCount_le_const_of_star_matching_pair
    {ι : Type v} [Finite ι] [Nonempty ι]
    (F : ι → FiniteSimpleGraph.{u})
    (hpair : FamilyContainsStarMatchingPair F) :
    ∃ C : ℕ, ∀ n (G : SimpleGraph (Fin n)), FamilyFree F G → edgeCount G ≤ C := by
  rcases hpair with ⟨⟨i, hstar⟩, ⟨j, hmatching⟩⟩
  let a : ℕ := Fintype.card (F i).V
  let b : ℕ := Fintype.card (F j).V
  refine ⟨2 * (b - 1) * (a - 1), ?_⟩
  intro n G hfree
  classical
  letI : DecidableRel G.Adj := Classical.decRel _
  have hmax : G.maxDegree ≤ a - 1 := by
    simpa [a] using
      (familyFree_maxDegree_le_pred_card_of_star
        (F := F) (i := i) hstar G hfree)
  rcases
      familyFree_exists_edgeCover_card_le_two_mul_pred_card_of_matching
        (F := F) (j := j) hmatching G hfree with
    ⟨T, hTcard, hcover⟩
  have hTcard' : T.card ≤ 2 * (b - 1) := by
    simpa [b] using hTcard
  exact
    edgeCount_le_two_mul_pred_mul_pred_of_maxDegree_and_edgeCover
      G a b T hmax hTcard' hcover

/--
The bounded direction added in the corrected paper: a star/matching obstruction
forces the family extremal function to be bounded.
-/
theorem families_star_matching_pair_O_one
    {ι : Type v} [Finite ι] [Nonempty ι]
    (F : ι → FiniteSimpleGraph.{u})
    (hpair : FamilyContainsStarMatchingPair F) :
    IsOConstant (fun n : ℕ => extremalFamily F n) := by
  rcases familyFree_edgeCount_le_const_of_star_matching_pair F hpair with ⟨C, hC⟩
  exact isOConstant_of_forall_le
    (fun n : ℕ => extremalFamily F n) C
    (extremalFamily_le_of_forall_edgeCount_le F C hC)

/-- With the individual linear hypotheses, the bounded direction is actually
`Θ(1)`. -/
theorem families_star_matching_pair_Theta_one
    {ι : Type v} [Finite ι] [Nonempty ι]
    (F : ι → FiniteSimpleGraph.{u})
    (hlinear : ∀ i : ι, IsThetaLinear (fun n : ℕ => (F i).extremal n))
    (hpair : FamilyContainsStarMatchingPair F) :
    IsThetaConstant (fun n : ℕ => extremalFamily F n) := by
  rcases familyFree_edgeCount_le_const_of_star_matching_pair F hpair with ⟨C, hC⟩
  have hUpper : ∀ n, extremalFamily F n ≤ C :=
    extremalFamily_le_of_forall_edgeCount_le F C hC
  have hTwo : ∀ i : ι, (F i).atLeastTwoEdgesAfterDeletingIsolated := by
    intro i
    exact singleForbiddenGraphLemma (F i) (hlinear i)
  exact isThetaConstant_of_forall_le_of_eventually_one_le
    (fun n : ℕ => extremalFamily F n) C hUpper
    (oneEdgeConstruction_extremalFamily_eventually_one_le F hTwo)

/-- If there is no star/matching obstruction, then the family extremal function
is linear. -/
theorem families_no_star_matching_pair
    {ι : Type v} [Finite ι] [Nonempty ι]
    (F : ι → FiniteSimpleGraph.{u})
    (hlinear : ∀ i : ι, IsThetaLinear (fun n : ℕ => (F i).extremal n))
    (hno : ¬ FamilyContainsStarMatchingPair F) :
    IsThetaLinear (fun n : ℕ => extremalFamily F n) := by
  classical
  let i0 : ι := Classical.choice (inferInstance : Nonempty ι)
  have hUpper : IsOLinear (fun n : ℕ => extremalFamily F n) :=
    extremalFamily_isOLinear_of_member F i0 (hlinear i0)
  have hTwo : ∀ i : ι, (F i).atLeastTwoEdgesAfterDeletingIsolated := by
    intro i
    exact singleForbiddenGraphLemma (F i) (hlinear i)
  have hLower : IsOmegaLinear (fun n : ℕ => extremalFamily F n) := by
    by_cases hStar : ∃ i : ι, (F i).starAfterDeletingIsolated
    · have hNoMatching : ∀ j : ι, ¬ (F j).matchingAfterDeletingIsolated := by
        intro j hj
        rcases hStar with ⟨i, hi⟩
        exact hno ⟨⟨i, ⟨hi, hTwo i⟩⟩, ⟨j, ⟨hj, hTwo j⟩⟩⟩
      exact isOmegaLinear_of_eventually_half_le
        (fun n : ℕ => extremalFamily F n)
        (matchingConstruction_extremalFamily_eventually_half_le
          F hTwo hNoMatching)
    · have hNoStar : ∀ i : ι, ¬ (F i).starAfterDeletingIsolated := by
        intro i hi
        exact hStar ⟨i, hi⟩
      exact isOmegaLinear_of_eventually_pred_le
        (fun n : ℕ => extremalFamily F n)
        (starConstruction_extremalFamily_eventually_pred_le
          F hTwo hNoStar)
  exact isThetaLinear_of_isOLinear_of_isOmegaLinear
    (fun n : ℕ => extremalFamily F n) hUpper hLower

/-- Formal dichotomy theorem for finite families. -/
theorem familiesTheorem
    {ι : Type v} [Finite ι] [Nonempty ι]
    (F : ι → FiniteSimpleGraph.{u})
    (hlinear : ∀ i : ι, IsThetaLinear (fun n : ℕ => (F i).extremal n)) :
    (FamilyContainsStarMatchingPair F ∧
        IsThetaConstant (fun n : ℕ => extremalFamily F n)) ∨
      (¬ FamilyContainsStarMatchingPair F ∧
        IsThetaLinear (fun n : ℕ => extremalFamily F n)) := by
  by_cases hpair : FamilyContainsStarMatchingPair F
  · exact Or.inl
      ⟨hpair, families_star_matching_pair_Theta_one F hlinear hpair⟩
  · exact Or.inr
      ⟨hpair, families_no_star_matching_pair F hlinear hpair⟩

end Erdos180
#print axioms Erdos180.familiesTheorem
