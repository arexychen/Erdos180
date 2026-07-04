import Erdos180.Families.Theorem
import Erdos180.Forest

open Filter
open Asymptotics

noncomputable section

namespace Erdos180

universe u v w

private theorem extremalFamily_isOLinear_of_forest_member
    {ι : Type v} [Finite ι]
    (F : ι → FiniteSimpleGraph.{u}) (i : ι)
    (hforest : (F i).reduced.IsAcyclic) :
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
  have hiO : IsOLinear (fun n : ℕ => (F i).extremal n) := by
    simpa [FiniteSimpleGraph.extremal, FiniteSimpleGraph.reduced] using
      (isOLinear_extremalNumber_of_deleteIsolated_isAcyclic
        (F i).graph hforest)
  unfold IsOLinear at hiO
  exact hToSingle.trans hiO

private theorem families_star_matching_pair_Theta_one_structural
    {ι : Type v} [Finite ι] [Nonempty ι]
    (F : ι → FiniteSimpleGraph.{u})
    (htwo : ∀ i : ι, (F i).atLeastTwoEdgesAfterDeletingIsolated)
    (hpair : FamilyContainsStarMatchingPair F) :
    IsThetaConstant (fun n : ℕ => extremalFamily F n) := by
  rcases familyFree_edgeCount_le_const_of_star_matching_pair F hpair with ⟨C, hC⟩
  have hUpper : ∀ n, extremalFamily F n ≤ C :=
    extremalFamily_le_of_forall_edgeCount_le F C hC
  exact isThetaConstant_of_forall_le_of_eventually_one_le
    (fun n : ℕ => extremalFamily F n) C hUpper
    (oneEdgeConstruction_extremalFamily_eventually_one_le F htwo)

private theorem families_no_star_matching_pair_structural
    {ι : Type v} [Finite ι] [Nonempty ι]
    (F : ι → FiniteSimpleGraph.{u})
    (hforest : ∀ i : ι, (F i).reduced.IsAcyclic)
    (htwo : ∀ i : ι, (F i).atLeastTwoEdgesAfterDeletingIsolated)
    (hno : ¬ FamilyContainsStarMatchingPair F) :
    IsThetaLinear (fun n : ℕ => extremalFamily F n) := by
  classical
  let i0 : ι := Classical.choice (inferInstance : Nonempty ι)
  have hUpper : IsOLinear (fun n : ℕ => extremalFamily F n) :=
    extremalFamily_isOLinear_of_forest_member F i0 (hforest i0)
  have hLower : IsOmegaLinear (fun n : ℕ => extremalFamily F n) := by
    by_cases hStar : ∃ i : ι, (F i).starAfterDeletingIsolated
    · have hNoMatching : ∀ j : ι, ¬ (F j).matchingAfterDeletingIsolated := by
        intro j hj
        rcases hStar with ⟨i, hi⟩
        exact hno ⟨⟨i, ⟨hi, htwo i⟩⟩, ⟨j, ⟨hj, htwo j⟩⟩⟩
      exact isOmegaLinear_of_eventually_half_le
        (fun n : ℕ => extremalFamily F n)
        (matchingConstruction_extremalFamily_eventually_half_le
          F htwo hNoMatching)
    · have hNoStar : ∀ i : ι, ¬ (F i).starAfterDeletingIsolated := by
        intro i hi
        exact hStar ⟨i, hi⟩
      exact isOmegaLinear_of_eventually_pred_le
        (fun n : ℕ => extremalFamily F n)
        (starConstruction_extremalFamily_eventually_pred_le
          F htwo hNoStar)
  exact isThetaLinear_of_isOLinear_of_isOmegaLinear
    (fun n : ℕ => extremalFamily F n) hUpper hLower

/-- Structural dichotomy theorem for finite families whose reduced members are
forests with at least two edges. -/
theorem familiesTheoremStructural
    {ι : Type v} [Finite ι] [Nonempty ι]
    (F : ι → FiniteSimpleGraph.{u})
    (hforest : ∀ i : ι, ((F i).reduced).IsAcyclic)
    (htwo : ∀ i : ι, (F i).atLeastTwoEdgesAfterDeletingIsolated) :
    (FamilyContainsStarMatchingPair F ∧
        IsThetaConstant (fun n : ℕ => extremalFamily F n)) ∨
      (¬ FamilyContainsStarMatchingPair F ∧
        IsThetaLinear (fun n : ℕ => extremalFamily F n)) := by
  by_cases hpair : FamilyContainsStarMatchingPair F
  · exact Or.inl
      ⟨hpair, families_star_matching_pair_Theta_one_structural F htwo hpair⟩
  · exact Or.inr
      ⟨hpair, families_no_star_matching_pair_structural F hforest htwo hpair⟩

/-- info: 'Erdos180.familiesTheoremStructural' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Erdos180.familiesTheoremStructural

end Erdos180
