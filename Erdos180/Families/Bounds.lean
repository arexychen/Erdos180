import Erdos180.SingleForbidden

open Filter
open Asymptotics

noncomputable section

namespace Erdos180

universe u v w

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

end Erdos180
