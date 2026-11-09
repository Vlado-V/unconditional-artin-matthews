module

public import ArtinMatthews.ShiftedABLDualTruncation
public import ArtinMatthews.ShiftedABLSourceBudget


set_option backward.privateInPublic true
@[expose] public section

/-! Quantitative truncation of the actual normalized circle dual.
The cutoff is chosen after the fixed circle exponent and desired saving,
using the uniform source derivatives. -/

noncomputable section
open Set OAI
open scoped ContDiff BigOperators

namespace ArtinMatthews

/-- The actual dual cutoff with the denominator varying over `[Q,2Q]`. -/
def shiftedABLThetaDualCutoff (M T P Q ε : ℝ) : ℝ := 4*Q^2/(M*T)*P^ε

private theorem shiftedABLThetaCircle_partial_error
    (χ : SevenEighths.HeckeFamily.Character) (W1 W2 : SchwartzMap ℝ ℂ)
    (K1 K2 : ℝ) (D m3 m4 F r L J B : ℕ) (hL : 0 < L)
    (S U C : ℝ) (hS : 0 < S) (hU : 0 < U) (hC : 0 ≤ C) (hJ : U ≤ (2 : ℝ)^J)
    (hdecay : ∀ q ∈ circleModuli F r L, ∀ k : ℕ,
      ‖thetaBesselCoeff χ W1 K1 ((q : ℝ)^2) k‖ ≤
        C*(1/(k : ℝ)^2)/(1+(k : ℝ)/S)^B ∧
      ‖thetaBesselCoeff χ W2 K2 ((q : ℝ)^2) k‖ ≤
        C*(1/(k : ℝ)^2)/(1+(k : ℝ)/S)^B) :
    ‖thetaDualNonzeroCircleAverage χ W1 W2 K1 K2 D m3 m4 F r L -
      ∑ d ∈ shiftedABLDualRectangle J, thetaDualDyadicCircleBlock χ W1 W2 K1 K2 D m3 m4 F r L d‖ ≤
      C^2*(S/U)^B*(∑' k : ℕ, 1/(k : ℝ)^2)^2 := by
  let Qs := circleModuli F r L
  let weight := circleSmoothWeight L
  let Λ := circleNormalizer Qs weight
  let f (q : ℕ) := thetaDualNonzeroNormalized χ W1 W2 K1 K2 D m3 m4 q -
    ∑ d ∈ shiftedABLDualRectangle J, thetaDualDyadicNormalized χ W1 W2 K1 K2 D m3 m4 q d
  let E := C^2*(S/U)^B*(∑' k : ℕ, 1/(k : ℝ)^2)^2
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hpos (q : ℕ) (hq : q ∈ Qs) : 0 < q :=
    (by omega : 0 < 3*L).trans_le (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).1
  have hmass : circleWeightMass Qs weight ≤ Λ := by
    unfold circleWeightMass
    change (∑ q ∈ Qs, weight q) ≤ ∑ q ∈ Qs, weight q * (q.totient : ℝ)
    apply Finset.sum_le_sum
    intro q hq
    have hφ : (1 : ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr (hpos q hq)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hφ (circleSmoothWeight_nonneg L q)
  have hΛ0 : 0 ≤ Λ := (circleWeightMass_nonneg Qs weight (fun q _ => circleSmoothWeight_nonneg L q)).trans hmass
  have heq : thetaDualNonzeroCircleAverage χ W1 W2 K1 K2 D m3 m4 F r L -
      ∑ d ∈ shiftedABLDualRectangle J, thetaDualDyadicCircleBlock χ W1 W2 K1 K2 D m3 m4 F r L d =
      (∑ q ∈ Qs, (weight q : ℂ)*f q)/(Λ : ℂ) := by
    simp only [thetaDualNonzeroCircleAverage, thetaDualDyadicCircleBlock, ← Finset.sum_div, ← sub_div]
    congr 1
    rw [Finset.sum_comm (s := shiftedABLDualRectangle J), ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro q _
    dsimp [f,weight]
    rw [mul_sub, Finset.mul_sum]
  rw [heq]
  rcases hΛ0.eq_or_lt with hΛ | hΛ
  · simp only [← hΛ, Complex.ofReal_zero, div_zero, norm_zero]
    exact hE
  · apply (circleAverage_norm_le Qs weight f E (fun q _ => circleSmoothWeight_nonneg L q)
      (fun q hq => shiftedABLThetaDualNormalized_partial_error χ W1 W2 K1 K2 D m3 m4 q J B
        (hpos q hq) S U C hS hU hC hJ (fun k => (hdecay q hq k).1)
        (fun k => (hdecay q hq k).2)) hΛ).trans
    exact mul_le_of_le_one_right hE ((div_le_one hΛ).2 hmass)

/-- With (A) and the positive cutoff exponent already fixed, the actual
nonzero circle dual differs from the finite sum of its literal smooth
blocks by an arbitrary negative source power. -/
theorem shiftedABLThetaCircle_dual_tail
    {A ε E : ℝ} (hA : 1 ≤ A) (hε : 0 < ε) (_hE : 0 ≤ E)
    (Cg : ℕ → ℝ) (hCg : ∀ j, 0 ≤ Cg j) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (χ : SevenEighths.HeckeFamily.Character) (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
        (M T m1 m2 : ℝ) (N D m3 m4 F r : ℕ) (_hM : 1 ≤ M) (hT : 1 ≤ T)
        (hgs : Function.support g ⊆ Icc T (2*T)),
        0 < N → M ≤ m1 → m1 ≤ 2*M → M ≤ m2 → m2 ≤ 2*M →
        (∀ j x, ‖iteratedDeriv j g x‖ ≤ Cg j/T^j) →
        let P := shiftedABLSourceParameter M T N
        let L := circlePowerScale P A
        let Q := circlePowerQ P A
        let U := shiftedABLThetaDualCutoff M T P Q ε
        let J := shiftedABLDualCutoffIndex U
        let W1 := shiftedABLThetaTestWeight g hg T m1 (zero_lt_one.trans_le hT) hgs
        let W2 := shiftedABLThetaMajorantWeight m2 T
        1 ≤ U ∧ U ≤ (2 : ℝ)^J ∧ (2 : ℝ)^J ≤ 2*U ∧
          ‖thetaDualNonzeroCircleAverage χ W1 W2 (m1*T) (m2*T) D m3 m4 F r L -
            ∑ d ∈ shiftedABLDualRectangle J,
              thetaDualDyadicCircleBlock χ W1 W2 (m1*T) (m2*T) D m3 m4 F r L d‖ ≤ C*P^(-E) := by
  let B : ℕ := ⌈(12*A+E)/ε⌉₊
  have hB : 12*A+E ≤ ε*(B : ℝ) := by
    have h := (div_le_iff₀ hε).1 (Nat.le_ceil ((12*A+E)/ε))
    linarith
  obtain ⟨C₁,hC₁,hdecay⟩ := shiftedABLThetaSource_coeff_decay B Cg hCg
  let V : ℝ := ∑' k : ℕ, 1/(k : ℝ)^2
  let C₀ := C₁*4^3*6^6
  let C := C₀^2*V^2+1
  have hC₀ : 0 < C₀ := by dsimp [C₀]; positivity
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro χ g hg M T m1 m2 N D m3 m4 F r hM hT hgs hN hm1 hm1' hm2 hm2' hderiv P L Q U J W1 W2
  let H := M*T
  let S := 4*Q^2/H
  have hH : 1 ≤ H := one_le_mul_of_one_le_of_one_le hM hT
  have hH0 : 0 < H := zero_lt_one.trans_le hH
  have hP : 1 ≤ P := shiftedABLSourceParameter_one_le hM hT hN
  have hP0 : 0 < P := zero_lt_one.trans_le hP
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hHP : H ≤ P := by
    change M*T ≤ T*M*(N : ℝ)
    nlinarith [mul_le_mul_of_nonneg_left hN1 (mul_nonneg (by linarith : 0 ≤ T) (by linarith : 0 ≤ M))]
  obtain ⟨hQ,hQup⟩ := shiftedABLSource_circleQ_bounds hP (zero_le_one.trans hA)
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ
  have hL : 0 < L := circlePowerScale_pos hP0
  have hHQ : H ≤ Q := hHP.trans
    ((by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hP hA :
      P ≤ P^A).trans circlePowerQ_lower)
  have hS : 0 < S := by dsimp [S]; positivity
  have hS1 : 1 ≤ S := by
    change 1 ≤ 4*Q^2/H
    apply (le_div_iff₀ hH0).2
    nlinarith [mul_le_mul_of_nonneg_right hQ hQ0.le]
  have hpow : 1 ≤ P^ε := Real.one_le_rpow hP hε.le
  have hU : 1 ≤ U := one_le_mul_of_one_le_of_one_le hS1 hpow
  have hU0 : 0 < U := zero_lt_one.trans_le hU
  obtain ⟨hJU,hUJ⟩ := shiftedABLDualCutoffIndex_bounds hU
  refine ⟨hU,hJU,hUJ, ?_⟩
  have hQ6 : Q^6 ≤ 6^6*P^(6*A) := by
    calc
      _ ≤ (6*P^A)^6 := pow_le_pow_left₀ hQ0.le hQup 6
      _ = _ := by
        rw [mul_pow, ← Real.rpow_natCast (P^A) 6, ← Real.rpow_mul hP0.le]
        norm_num
        rw [mul_comm A 6]
  have hSize : C₁*H*S^3 ≤ C₀*P^(6*A) := by
    calc
      _ = C₁*4^3*Q^6/H^2 := by
        change C₁*H*(4*Q^2/H)^3 = _
        field_simp [hH0.ne']
      _ ≤ C₁*4^3*Q^6 := div_le_self (by positivity) (one_le_pow₀ hH)
      _ ≤ C₁*4^3*(6^6*P^(6*A)) := mul_le_mul_of_nonneg_left hQ6 (by positivity)
      _ = _ := by dsimp [C₀]; ring
  have hTail := shiftedABLThetaCircle_partial_error χ W1 W2 (m1*T) (m2*T)
    D m3 m4 F r L J B hL S U (C₁*H*S^3) hS hU0 (by positivity) hJU
    (fun q hq k => by
      have hqI := Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1
      have hq0 : 0 < q := (by omega : 0 < 3*L).trans_le hqI.1
      have hqR : (0 : ℝ) < q := by exact_mod_cast hq0
      have hqQ : (q : ℝ) ≤ 2*Q := by
        calc
          (q : ℝ) ≤ ((6*L : ℕ) : ℝ) := by exact_mod_cast hqI.2
          _ = 2*Q := by change _ = 2*(3*(L : ℝ)); push_cast; ring
      exact hdecay χ g hg M T m1 m2 Q q hM hT hgs hm1 hm1' hm2 hm2' hqR hqQ hderiv k)
  apply hTail.trans
  change (C₁*H*S^3)^2*(S/U)^B*V^2 ≤ C*P^(-E)
  have hRatio : S/U = P^(-ε) := by
    change S/(S*P^ε) = P^(-ε)
    rw [Real.rpow_neg hP0.le, div_mul_eq_div_div, div_self hS.ne', one_div]
  have hRatioPow : (S/U)^B = P^(-(ε*(B : ℝ))) := by
    rw [hRatio, ← Real.rpow_natCast (P^(-ε)) B, ← Real.rpow_mul hP0.le]
    congr 1
    ring
  have hP12 : (P^(6*A))^2 = P^(12*A) := by
    rw [← Real.rpow_natCast (P^(6*A)) 2, ← Real.rpow_mul hP0.le]
    congr 1
    push_cast
    ring
  calc
    _ ≤ (C₀*P^(6*A))^2*(S/U)^B*V^2 := by gcongr
    _ = (C₀^2*V^2)*P^(12*A-ε*(B : ℝ)) := by
      rw [mul_pow, hP12, hRatioPow, Real.rpow_sub hP0, Real.rpow_neg hP0.le]
      ring
    _ ≤ (C₀^2*V^2)*P^(-E) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hP (by linarith)) (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (Real.rpow_nonneg hP0.le _)

end ArtinMatthews
