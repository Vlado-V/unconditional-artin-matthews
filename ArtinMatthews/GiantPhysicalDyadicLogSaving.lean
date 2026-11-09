module

public import ArtinMatthews.GiantPhysicalCutoffDyadic


set_option backward.privateInPublic true
@[expose] public section

/-! A uniform dyad estimate pays for the entire physical cutoff sum.
The low dyads vanish because the dilation is a positive integer. -/
namespace ArtinMatthews
open Filter Finset
open scoped BigOperators
noncomputable section

theorem giantPhysicalDyadicCount_le_log_sq {x : ℝ} (hx : 2 ≤ x)
    (hL : 1 + 3 / Real.log 2 ≤ Real.log x) {N : ℕ} (hN : (N : ℝ) ≤ x^2) :
    ((Nat.log 2 N + 1 : ℕ) : ℝ) ≤ (Real.log x)^2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL1 : 1 ≤ Real.log x :=
    (le_add_of_nonneg_right (div_nonneg (by norm_num) hlog2.le)).trans hL
  have hN' : (N : ℝ) + 1 ≤ x^3 := calc
    _ ≤ x^2 + 1 := add_le_add hN le_rfl
    _ ≤ 2 * x^2 := by nlinarith only [sq_nonneg (x - 1), hx]
    _ ≤ x * x^2 := mul_le_mul_of_nonneg_right hx (sq_nonneg x)
    _ = x^3 := by ring
  have hlogN : Real.log ((N : ℝ)+1) ≤ 3 * Real.log x := by
    have h := Real.log_le_log (by positivity : 0 < (N : ℝ)+1) hN'
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  calc
    _ ≤ 1 + Real.log ((N : ℝ)+1) / Real.log 2 := primeExtractionDyadicIndex_count_le N
    _ ≤ 1 + 3 * Real.log x / Real.log 2 :=
      add_le_add le_rfl (div_le_div_of_nonneg_right hlogN hlog2.le)
    _ ≤ (1 + 3 / Real.log 2) * Real.log x := by
      calc
        _ ≤ Real.log x + 3 * Real.log x / Real.log 2 := add_le_add hL1 le_rfl
        _ = _ := by ring
    _ ≤ _ := by rw [pow_two]; exact mul_le_mul_of_nonneg_right hL (zero_le_one.trans hL1)

theorem giantTwoSidedPhysicalCutoffPairing_log_saving_of_dyads
    {I J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ}
    {k ell : ℕ} {Z : Finset ℕ} (hP : ∀ j p, p ∈ P j → p.Prime)
    (patterns : Finset I) (C : I → J → Finset (Fin k)) (step : ℤ) (q ζ : ℝ)
    (K : ∀ p, GiantTwoSidedPatternCoefficient P (C p) ell) (Ψ : ℝ → ℂ)
    {x a τ : ℝ} (hx : 2 ≤ x) (ha : 0 < a) (hsmall : 2 * x^τ ≤ a * x)
    (hL : 1 + 3 / Real.log 2 ≤ Real.log x) (hΨ : ∀ t < a, Ψ t = 0)
    (f : ℕ → ℂ) (g : GiantTwoSidedEndpointState P (k+ell) Z → ℂ) (N : ℕ)
    (hZ : Z ⊆ Ioc 0 N) (hN : (N : ℝ) ≤ x^2) (E : ℝ)
    (hblock : ∀ j ∈ range (Nat.log 2 N + 1), x^τ ≤ ((2 ^ j : ℕ) : ℝ) →
      ‖giantTwoSidedPhysicalCutoffPairing patterns C step q ζ K Ψ x
        (giantPhysicalDyadicLeft ((2 ^ j : ℕ) : ℝ) f) g‖ ≤ (Real.log x)^(-(E+2))) :
    ‖giantTwoSidedPhysicalCutoffPairing patterns C step q ζ K Ψ x f g‖ ≤ (Real.log x)^(-E) := by
  have hx0 : 0 < x := zero_lt_two.trans_le hx
  have hL0 : 0 < Real.log x := Real.log_pos ((by norm_num : (1 : ℝ) < 2).trans_le hx)
  let L := Real.log x
  let indices := range (Nat.log 2 N + 1)
  let B (j : ℕ) := giantTwoSidedPhysicalCutoffPairing patterns C step q ζ K Ψ x
    (giantPhysicalDyadicLeft ((2 ^ j : ℕ) : ℝ) f) g
  have hj (j : ℕ) (hj : j ∈ indices) : ‖B j‖ ≤ L^(-(E+2)) := by
    by_cases hX : x^τ ≤ ((2 ^ j : ℕ) : ℝ)
    · exact hblock j hj hX
    · have hlow : 2 * ((2 ^ j : ℕ) : ℝ) ≤ a * x :=
        (mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge hX)) zero_le_two).trans hsmall
      have hz : B j = 0 := giantTwoSidedPhysicalCutoffPairing_dyadic_eq_zero hP
        patterns C step q ζ K Ψ hx0 ha hlow hΨ f g
      rw [hz, norm_zero]
      exact Real.rpow_nonneg hL0.le _
  rw [giantTwoSidedPhysicalCutoffPairing_eq_dyadic patterns C step q ζ K Ψ x f g N hZ]
  change ‖∑ j ∈ indices, B j‖ ≤ L^(-E)
  calc
    _ ≤ ∑ j ∈ indices, ‖B j‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ indices, L^(-(E+2)) := sum_le_sum hj
    _ = ((Nat.log 2 N + 1 : ℕ) : ℝ) * L^(-(E+2)) := by simp [indices]
    _ ≤ L^2 * L^(-(E+2)) := mul_le_mul_of_nonneg_right
      (giantPhysicalDyadicCount_le_log_sq hx hL hN) (Real.rpow_nonneg hL0.le _)
    _ = _ := by
      rw [← Real.rpow_two, ← Real.rpow_add hL0]
      congr 1
      ring

end
end ArtinMatthews
