module

public import ArtinMatthews.CubicSieveRetainedActualError
public import ArtinMatthews.CubicSieveRetainedMain
public import ArtinMatthews.CubicSieveActualJointEuler
public import ArtinMatthews.CubicSievePoleNormalization
public import ArtinMatthews.CubicSieveArrayReplacement
public import ArtinMatthews.CubicSieveRoughCorollary


set_option backward.privateInPublic true
@[expose] public section

/-! Proposition 7.1 for the actual distinct marking array. All retained
and discarded arithmetic errors are discharged. -/

noncomputable section
namespace ArtinMatthews

universe u

open Filter Finset
open scoped BigOperators ContDiff Topology

theorem cubicSieve_actual_divisorWeighted_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (J : Type u) [Fintype J] [DecidableEq J], ∀ (e : J → ℝ), (∀ j, 0 < e j ∧ e j ≤ 1 / 5) →
      Function.Injective e → ∀ (α : ℝ), 0 < α → (∀ j, α ≤ e j) →
      ∀ (Φ : ℝ → ℝ), ContDiff ℝ ∞ Φ → (∀ t, |Φ t| ≤ 1) →
        Function.support Φ ⊆ Set.Ioo 1 2 →
      ∀ (ε : ℝ), 0 < ε → ε < 1 / 4 → ∀ m : ℕ, 1 ≤ m →
        CubicSieveDivisorWeightedBound e Φ ε m C := by
  obtain ⟨C, hC, hmodel⟩ := cubicSieve_divisorModel_log_bounds
  refine ⟨6 * C, by positivity, ?_⟩
  intro J instF instD e he hinj α hα heα Φ hΦ hΦ₁ hs ε hε hεq m hm δ hδ
  let γ := cubicSieveSourceExponent ε m
  have hγs := cubicSieve_sourceExponent_bounds hε hεq m
  have hγ : 0 < γ := hγs.1
  have hγ1 : γ ≤ 1 := hγs.2.1.le.trans (by norm_num)
  have hlev : γ * (8 * (m : ℝ) + 2) ≤ 1 / 16 := by
    have h := hγs.2.2
    dsimp only [γ] at h ⊢
    linarith
  let w₀ : ℝ := (1 / 2 : ℝ) ^ Fintype.card J
  have hw₀ : 0 < w₀ := by dsimp only [w₀]; positivity
  have hMean := literalMarkedArrayMean_lower_eventually e (fun j => (he j).1)
  have hM := (tendsto_rpow_atTop hγ).eventually hmodel
  have hJ := cubicSieve_actualJointEuler_log_saving e he hinj hα heα hγ m 3 zero_lt_one
  have hR := cubicSieve_retainedActual_error_log_saving e he hinj Φ hΦ hs hγ m hlev 2
  have hA := cubicSieve_overflow_arrayReplacement_log_saving e he hinj (fun _ => 1)
    (fun _ => by norm_num) Φ hΦ₁ 2
  have hL := Real.tendsto_log_atTop.eventually (eventually_ge_atTop
    (max 1 (max (Real.log 3 + 2 * |Real.eulerMascheroniConstant|) (8 / (w₀ * δ)))))
  filter_upwards [hMean, hM, hJ, hR, hA, hL, eventually_gt_atTop (1 : ℝ)]
    with x hxW hxM hxJ hxR hxA hxL hx₁
  let P := fun j => markedLogPowerBand (e j) x
  let V := fun j => bandReciprocalMass (P j)
  let k := cubicSamplingTruncationDepth x
  let L := Real.log x
  let W := literalMarkedArrayMean e x
  let z := x ^ γ
  let S := cubicSieveDivisorWeightedError e Φ γ x m
  let T := cubicSieveRetainedWeightedSum P V Φ z x m k
  let M := cubicSieveRetainedProgressionModel P V Φ z x m k
  let J₀ := cubicSieveJointEulerModel P V z m k 1
  let J₁ := deriv (cubicSieveJointEulerModel P V z m k) 1
  let H₀ := cubicSieveDivisorCorrectionModel z m 1
  let H₁ := deriv (cubicSieveDivisorCorrectionModel z m) 1
  let E := Real.exp (-(2 * (m : ℝ)))
  have hx₀ := zero_lt_one.trans hx₁
  have hL₀ : 0 < L := Real.log_pos hx₁
  have hL₁ : 1 ≤ L := (le_max_left _ _).trans hxL
  have hW : 0 < W := hw₀.trans_le hxW
  have hlogz : Real.log z = γ * L := Real.log_rpow hx₀ γ
  have hneg2 : L ^ (-(2 : ℝ)) = 1 / L ^ (2 : ℕ) := by
    rw [Real.rpow_neg hL₀.le, Real.rpow_ofNat L 2, one_div]
  have hneg3 : L ^ (-(3 : ℝ)) = 1 / L ^ (3 : ℕ) := by
    rw [Real.rpow_neg hL₀.le, Real.rpow_ofNat L 3, one_div]
  have hST : |S - T| ≤ x / L ^ 2 := by
    have h := hxA z (Real.rpow_nonneg hx₀.le γ) m
    dsimp only at h
    have heq : S - T = ∑ u ∈ Icc 1 ⌊2 * x⌋₊, Φ ((u : ℝ) / x) *
        ((∏ j, (bandWeight (P j) (V j) u) ^ (1 : ℕ)) - cubicSamplingArrayTruncation P V (fun _ => 1) k u) *
        ((u + 1).divisors.card : ℝ) * cubicSieveCorrection z m (u + 1) := by
      dsimp only [S, T, cubicSieveDivisorWeightedError, cubicSieveRetainedWeightedSum]
      rw [← sum_sub_distrib]
      apply sum_congr rfl
      intro u _
      simp only [literalMarkedArrayWeight, divisorWeight, pow_one]
      ring
    rw [heq]
    change _ ≤ x * L ^ (-(2 : ℝ)) at h
    rw [hneg2] at h
    simpa only [mul_one_div] using h
  have hTM : |T - M| ≤ x / L ^ 2 := by
    change |T - M| ≤ x * L ^ (-(2 : ℝ)) at hxR
    rw [hneg2] at hxR
    simpa only [mul_one_div] using hxR
  have hSM : S ≤ |M| + 2 * x / L ^ 2 := by
    have h := abs_sub_le S T M
    have h' := abs_sub_le S M 0
    simp only [sub_zero] at h'
    have hd : |S - M| ≤ 2 * x / L ^ 2 :=
      h.trans ((add_le_add hST hTM).trans_eq (by ring))
    calc
      S ≤ |S| := le_abs_self S
      _ ≤ |S - M| + |M| := h'
      _ ≤ 2 * x / L ^ 2 + |M| := add_le_add hd le_rfl
      _ = _ := add_comm _ _
  have hmodel₀ := hxM m hm
  have hH₀ : 0 ≤ H₀ := hmodel₀.1
  have hH : H₀ ≤ C * E / (γ ^ 2 * L ^ 2) := by
    have h := hmodel₀.2.1
    rw [hlogz, mul_pow] at h
    exact h
  have hH' : |H₁| ≤ C * E / (γ * L) := by
    have h := hmodel₀.2.2
    rwa [hlogz] at h
  have hJ₀ : |J₀| ≤ W * C * E / (γ ^ 2 * L ^ 2) + 1 / L ^ 3 := by
    have h := abs_sub_le J₀ (W * H₀) 0
    simp only [sub_zero, abs_mul, abs_of_pos hW, abs_of_nonneg hH₀] at h
    have hj : |J₀ - W * H₀| ≤ 1 / L ^ 3 := by
      have h := hxJ.1
      change |J₀ - W * H₀| ≤ 1 * L ^ (-(3 : ℝ)) at h
      simpa only [one_mul, hneg3] using h
    have hm := mul_le_mul_of_nonneg_left hH hW.le
    exact h.trans ((add_le_add hj hm).trans_eq (by ring))
  have hJ₁ : |J₁| ≤ W * C * E / (γ * L) + 1 / L ^ 3 := by
    have h := abs_sub_le J₁ (W * H₁) 0
    simp only [sub_zero, abs_mul, abs_of_pos hW] at h
    have hj : |J₁ - W * H₁| ≤ 1 / L ^ 3 := by
      have h := hxJ.2
      change |J₁ - W * H₁| ≤ 1 * L ^ (-(3 : ℝ)) at h
      simpa only [one_mul, hneg3] using h
    have hm := mul_le_mul_of_nonneg_left hH' hW.le
    exact h.trans ((add_le_add hj hm).trans_eq (by ring))
  have hPr (j : J) (p : ℕ) (hp : p ∈ P j) : p.Prime := (mem_markedLogPowerBand.mp hp).1
  have hPole : |M| ≤ 2 * x * (2 * L * |J₀| + |J₁|) := by
    change |cubicSieveRetainedProgressionModel P V Φ z x m k| ≤ _
    rw [cubicSieve_retainedProgressionModel_eq_integral P V hPr Φ hΦ z hx₀ m k]
    exact cubicSieve_poleIntegral_abs_le Φ hΦ₁ hx₁
      ((le_max_left _ _).trans ((le_max_right _ _).trans hxL)) J₀ J₁
  have hsmall : 8 / (W * L) ≤ δ := by
    have hLbig : 8 / (w₀ * δ) ≤ L :=
      (le_max_right _ _).trans ((le_max_right _ _).trans hxL)
    have hmul := (div_le_iff₀ (mul_pos hw₀ hδ)).mp hLbig
    apply (div_le_iff₀ (mul_pos hW hL₀)).mpr
    have hw := mul_le_mul_of_nonneg_left hxW (mul_nonneg hδ.le hL₀.le)
    nlinarith only [hmul, hw]
  change L / (x * W) * S ≤ (6 * C) * E / γ ^ 2 + δ
  calc
    _ ≤ L / (x * W) * (2 * x * (2 * L * |J₀| + |J₁|) + 2 * x / L ^ 2) :=
      mul_le_mul_of_nonneg_left (hSM.trans (add_le_add hPole le_rfl)) (by positivity)
    _ ≤ 6 * C * E / γ ^ 2 + 8 / (W * L) :=
      cubicSieve_pole_normalized_envelope hx₀ hL₁ hW hγ hγ1 hC.le (Real.exp_pos _).le hJ₀ hJ₁
    _ ≤ _ := add_le_add le_rfl hsmall

private theorem cubicSieve_positiveArray_lower {J : Type*} [Fintype J]
    (e : J → ℝ) (he : ∀ j, 0 < e j) : ∃ α : ℝ, 0 < α ∧ ∀ j, α ≤ e j := by
  classical
  have h : ∀ S : Finset J, ∃ α : ℝ, 0 < α ∧ ∀ j ∈ S, α ≤ e j := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert j S _ ih =>
      obtain ⟨α, hα, hbound⟩ := ih
      refine ⟨min α (e j), lt_min hα (he j), ?_⟩
      intro i hi
      rcases mem_insert.mp hi with rfl | hi
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hbound i hi)
  obtain ⟨α, hα, hbound⟩ := h univ
  exact ⟨α, hα, fun j => hbound j (mem_univ j)⟩

theorem cubicSieve_actual_divisorWeighted_bound_finite :
    ∃ C : ℝ, 0 < C ∧ ∀ (J : Type u) [Fintype J] [DecidableEq J], ∀ (e : J → ℝ), (∀ j, 0 < e j ∧ e j ≤ 1 / 5) →
      Function.Injective e → ∀ (Φ : ℝ → ℝ), ContDiff ℝ ∞ Φ → (∀ t, |Φ t| ≤ 1) →
        Function.support Φ ⊆ Set.Ioo 1 2 →
      ∀ (ε : ℝ), 0 < ε → ε < 1 / 4 → ∀ m : ℕ, 1 ≤ m →
        CubicSieveDivisorWeightedBound e Φ ε m C := by
  obtain ⟨C, hC, hbound⟩ := cubicSieve_actual_divisorWeighted_bound.{u}
  refine ⟨C, hC, ?_⟩
  intro J instF instD e he hinj Φ hΦ hΦ₁ hs ε hε hεq m hm
  obtain ⟨α, hα, heα⟩ := cubicSieve_positiveArray_lower e (fun j => (he j).1)
  exact hbound J e he hinj α hα heα Φ hΦ hΦ₁ hs ε hε hεq m hm

end ArtinMatthews
