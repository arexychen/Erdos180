import Erdos180.ReducedEdge

open Filter
open Asymptotics

noncomputable section

namespace Erdos180

universe u v w

/--
Single-forbidden-graph lemma: `ex(n; H) = Θ(n)` iff the non-isolated part of
`H` is a forest with at least two edges.
-/
theorem singleForbiddenGraphLemma (H : FiniteSimpleGraph.{u}) :
    IsThetaLinear (fun n : ℕ => H.extremal n) →
      H.atLeastTwoEdgesAfterDeletingIsolated := by
  intro hTheta
  by_contra hnot
  have hred : edgeCount H.reduced ≤ 1 := by
    unfold FiniteSimpleGraph.atLeastTwoEdgesAfterDeletingIsolated at hnot
    omega
  let C := (Fintype.card H.V).choose 2
  have hBound : ∀ n, H.extremal n ≤ C := by
    apply extremalNumber_le_of_forall_edgeCount_le H C
    intro m G hfree
    by_cases hcard : Fintype.card H.V ≤ m
    · by_cases hpos : 0 < edgeCount G
      · exact False.elim <| hfree
          (embeds_of_reduced_edgeCount_le_one H G hred hcard hpos)
      · push_neg at hpos
        omega
    · push_neg at hcard
      calc
        edgeCount G ≤ m.choose 2 := edgeCount_le_complete_bound G
        _ ≤ (Fintype.card H.V).choose 2 :=
          Nat.choose_le_choose 2 hcard.le
  exact not_isThetaLinear_of_isOConstant
    (fun n : ℕ => H.extremal n)
    (isOConstant_of_forall_le _ C hBound) hTheta

end Erdos180
