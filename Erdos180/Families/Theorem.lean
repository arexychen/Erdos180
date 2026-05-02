import Erdos180.Families.Upper

open Filter
open Asymptotics

noncomputable section

namespace Erdos180

universe u v w

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
