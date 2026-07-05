import Erdos180.Core

open Filter
open Asymptotics

noncomputable section

namespace Erdos180

universe u v w

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

/-- A pointwise linear natural upper bound gives `O(n)`. -/
theorem isOLinear_of_forall_le_mul
    (f : ℕ → ℕ) (C : ℕ) (hC : ∀ n, f n ≤ C * n) :
    IsOLinear f := by
  unfold IsOLinear
  refine IsBigO.of_bound (C : ℝ) (Filter.Eventually.of_forall ?_)
  intro n
  have hreal : (f n : ℝ) ≤ (C * n : ℕ) := by
    exact_mod_cast hC n
  simpa [Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc] using hreal

/-- info: 'Erdos180.isOLinear_of_forall_le_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Erdos180.isOLinear_of_forall_le_mul

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


end Erdos180
