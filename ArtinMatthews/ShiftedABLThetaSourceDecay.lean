module

public import ArtinMatthews.ShiftedSourceBessel
public import ArtinMatthews.CubicThetaBesselSummable
public import Mathlib.Analysis.PSeries


set_option backward.privateInPublic true
@[expose] public section

/-! Uniform rapid decay of the two literal ideal-theta source coefficients.
The polynomial bound for the genuine ideal sums supplies the summable
reciprocal-square majorant. -/

noncomputable section
open Set OAI
open scoped ContDiff

namespace ArtinMatthews

/-- The normalized actual first source, at the length `m*T`. -/
def shiftedABLThetaTestWeight (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (T m : ℝ) (hT : 0 < T) (hgs : Function.support g ⊆ Icc T (2*T)) :
    SchwartzMap ℝ ℂ :=
  shiftedSourceTranslate (normalizedSourceSchwartz g hg T hT hgs) (1/(m*T))

/-- The fixed plateau in the same normalized coordinates. -/
def shiftedABLThetaMajorantWeight (m T : ℝ) : SchwartzMap ℝ ℂ :=
  shiftedSourceTranslate sourcePlateauSchwartz (1/(m*T))

private theorem thetaBesselCoeff_scaled_decay
    (χ : SevenEighths.HeckeFamily.Character) (W : SchwartzMap ℝ ℂ)
    (K q S C : ℝ) (J : ℕ) (hq : 0 < q) (hS : 0 < S)
    (hqK : q^2 ≤ S*K)
    (hB : ∀ k : ℕ, 0 < k →
      (1+K*((k : ℝ)/q^2))^(J+3) *
        ‖weightOneBesselTransform (fun x => W (x/K)) ((k : ℝ)/q^2)‖ ≤ C*K)
    (k : ℕ) :
    ‖thetaBesselCoeff χ W K (q^2) k‖ ≤
      (128*C*K*S^3) * (1/(k : ℝ)^2) / (1+(k : ℝ)/S)^J := by
  by_cases hk : k = 0
  · simp [hk, thetaBesselCoeff_zero]
  have hk0 : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast Nat.pos_of_ne_zero hk
  let t := 1+(k : ℝ)/S
  let u := 1+K*((k : ℝ)/q^2)
  let b := ‖weightOneBesselTransform (fun x => W (x/K)) ((k : ℝ)/q^2)‖
  have ht : 0 < t := by dsimp [t]; positivity
  have htu : t ≤ u := by
    dsimp [t,u]
    rw [← mul_div_assoc]
    refine add_le_add le_rfl ?_
    apply (div_le_div_iff₀ hS (sq_pos_of_pos hq)).2
    calc
      _ ≤ (k : ℝ)*(S*K) := mul_le_mul_of_nonneg_left hqK hk0.le
      _ = _ := by ring
  have hb : u^(J+3)*b ≤ C*K := hB k (Nat.pos_of_ne_zero hk)
  have hpow : ((k : ℝ)/S)^3 * t^J ≤ u^(J+3) := by
    have hkt : (k : ℝ)/S ≤ t := by dsimp [t]; linarith
    calc
      _ ≤ u^3*u^J := mul_le_mul
        (pow_le_pow_left₀ (by positivity) (hkt.trans htu) 3)
        (pow_le_pow_left₀ ht.le htu J) (by positivity)
        (pow_nonneg (ht.le.trans htu) 3)
      _ = _ := by rw [pow_add]; ring
  have hb' : (k : ℝ)^3*t^J*b ≤ C*K*S^3 := by
    calc
      _ = (((k : ℝ)/S)^3*t^J*b)*S^3 := by field_simp [hS.ne']
      _ ≤ (u^(J+3)*b)*S^3 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpow (norm_nonneg _)) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right hb (by positivity)
  have hCoeff : ‖idealThetaCoeff χ k‖ ≤ 128*(k : ℝ) :=
    (idealThetaCoeff_norm_le χ k).trans (by linarith)
  rw [thetaBesselCoeff, norm_mul, mul_one_div]
  change ‖idealThetaCoeff χ k‖ * b ≤ ((128*C*K*S^3)/(k : ℝ)^2)/t^J
  apply (le_div_iff₀ (pow_pos ht J)).2
  apply (le_div_iff₀ (sq_pos_of_pos hk0)).2
  calc
    _ ≤ (128*(k : ℝ)*b)*t^J*(k : ℝ)^2 := by gcongr
    _ = 128*((k : ℝ)^3*t^J*b) := by ring
    _ ≤ _ := by linarith [mul_le_mul_of_nonneg_left hb' (by norm_num : (0 : ℝ) ≤ 128)]

/-- For every fixed decay order and prescribed source derivative family,
a single bound works for both actual sources, every ideal character, and
all moduli `q ≤ 2Q`. -/
theorem shiftedABLThetaSource_coeff_decay (J : ℕ)
    (Cg : ℕ → ℝ) (hCg : ∀ j, 0 ≤ Cg j) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (χ : SevenEighths.HeckeFamily.Character) (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
        (M T m1 m2 Q q : ℝ) (_hM : 1 ≤ M) (hT : 1 ≤ T)
        (hgs : Function.support g ⊆ Icc T (2*T)),
        M ≤ m1 → m1 ≤ 2*M → M ≤ m2 → m2 ≤ 2*M →
        0 < q → q ≤ 2*Q → (∀ j x, ‖iteratedDeriv j g x‖ ≤ Cg j/T^j) →
        let S := 4*Q^2/(M*T)
        let W1 := shiftedABLThetaTestWeight g hg T m1 (zero_lt_one.trans_le hT) hgs
        let W2 := shiftedABLThetaMajorantWeight m2 T
        ∀ k : ℕ,
          ‖thetaBesselCoeff χ W1 (m1*T) (q^2) k‖ ≤
            (C*(M*T)*S^3) * (1/(k : ℝ)^2) / (1+(k : ℝ)/S)^J ∧
          ‖thetaBesselCoeff χ W2 (m2*T) (q^2) k‖ ≤
            (C*(M*T)*S^3) * (1/(k : ℝ)^2) / (1+(k : ℝ)/S)^J := by
  obtain ⟨L,C₁,hC₁,hfirst⟩ := shiftedSourceTest_bessel_denominator_bound (J+3) 0
  obtain ⟨C₂,hC₂,hsecond⟩ := shiftedSourceMajorant_bessel_denominator_bound (J+3) 0
  let G := ∑ j ∈ Finset.range (L+1), Cg j
  have hG : 0 ≤ G := Finset.sum_nonneg (fun j _ => hCg j)
  let C := 256*(C₁*G+C₂)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro χ g hg M T m1 m2 Q q hM hT hgs hm1 hm1' hm2 hm2' hq hqQ hderiv S W1 W2 k
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hH : 1 ≤ M*T := one_le_mul_of_one_le_of_one_le hM hT
  have hS : 0 < S := by
    have hQ : 0 < Q := by linarith
    change 0 < 4*Q^2/(M*T)
    positivity
  have hm10 : 0 < m1 := zero_lt_one.trans_le (hM.trans hm1)
  have hm20 : 0 < m2 := zero_lt_one.trans_le (hM.trans hm2)
  have hscale1 : 1 ≤ m1*T := one_le_mul_of_one_le_of_one_le (hM.trans hm1) hT
  have hscale2 : 1 ≤ m2*T := one_le_mul_of_one_le_of_one_le (hM.trans hm2) hT
  have hqS {m : ℝ} (hm : M ≤ m) : q^2 ≤ S*(m*T) := by
    have heq : S*(M*T) = 4*Q^2 := by
      change 4*Q^2/(M*T)*(M*T) = _
      exact div_mul_cancel₀ _ (zero_lt_one.trans_le hH).ne'
    calc
      _ ≤ (2*Q)^2 := pow_le_pow_left₀ hq.le hqQ 2
      _ = S*(M*T) := by rw [heq]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hm hT0.le) hS.le
  have hGbound (j : ℕ) (hj : j ≤ L) (x : ℝ) : ‖iteratedDeriv j g x‖ ≤ G/T^j :=
    (hderiv j x).trans (div_le_div_of_nonneg_right
      (Finset.single_le_sum (fun i _ => hCg i) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)))
      (pow_nonneg hT0.le _))
  have hW1 : (fun x : ℝ => W1 (x/(m1*T))) = shiftedSourceTest g m1 := by
    funext x
    exact (shiftedSourceTest_eq_normalized g hg T m1 hT0 hm10 hgs x).symm
  have hW2 : (fun x : ℝ => W2 (x/(m2*T))) = shiftedSourceMajorant m2 T := by
    funext x
    exact (shiftedSourceMajorant_eq_normalized m2 T x).symm
  have hfirst' (n : ℕ) (hn : 0 < n) :
      (1+(m1*T)*((n : ℝ)/q^2))^(J+3) *
        ‖weightOneBesselTransform (fun x => W1 (x/(m1*T))) ((n : ℝ)/q^2)‖ ≤
        (C₁*G)*(m1*T) := by
    rw [hW1]
    simpa only [LocalLogFourier.eulerDeriv, iteratedDeriv_zero, Real.exp_zero, mul_one,
      pow_zero, one_mul] using
      hfirst g hg T m1 G hT0 hm10 hG hgs hscale1 hGbound n q (by exact_mod_cast hn) hq 0 le_rfl
  have hsecond' (n : ℕ) (hn : 0 < n) :
      (1+(m2*T)*((n : ℝ)/q^2))^(J+3) *
        ‖weightOneBesselTransform (fun x => W2 (x/(m2*T))) ((n : ℝ)/q^2)‖ ≤ C₂*(m2*T) := by
    rw [hW2]
    simpa only [LocalLogFourier.eulerDeriv, iteratedDeriv_zero, Real.exp_zero, mul_one,
      pow_zero, one_mul] using
      hsecond T m2 hT0 hm20 hscale2 n q (by exact_mod_cast hn) hq 0 le_rfl
  have hC₁G : 0 ≤ C₁*G := mul_nonneg hC₁.le hG
  have hcompare {m B : ℝ} (hm0 : 0 ≤ m) (hm : m ≤ 2*M) (hBC : B ≤ C₁*G+C₂) :
      128*B*(m*T)*S^3 ≤ C*(M*T)*S^3 := by
    calc
      _ ≤ 128*(C₁*G+C₂)*(2*M*T)*S^3 := by
        have hm' := mul_le_mul_of_nonneg_right hm hT0.le
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul (mul_le_mul_of_nonneg_left hBC (by norm_num))
            hm' (mul_nonneg hm0 hT0.le)
            (mul_nonneg (by norm_num) (add_nonneg hC₁G hC₂.le))) (pow_nonneg hS.le _)
      _ = _ := by dsimp [C]; ring
  constructor
  · apply (thetaBesselCoeff_scaled_decay χ W1 (m1*T) q S (C₁*G) J hq hS
      (hqS hm1) hfirst' k).trans
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right (hcompare hm10.le hm1' (by linarith)) (by positivity)
  · apply (thetaBesselCoeff_scaled_decay χ W2 (m2*T) q S C₂ J hq hS
      (hqS hm2) hsecond' k).trans
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right (hcompare hm20.le hm2' (by linarith)) (by positivity)

end ArtinMatthews
