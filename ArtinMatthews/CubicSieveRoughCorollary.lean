module

public import ArtinMatthews.CubicSieveRoughError


set_option backward.privateInPublic true
@[expose] public section

/-! Corollary 7.2 with the literal divisor-weighted Proposition 7.1
estimate exposed as a separate input. The upper polynomial is controlled
by the actual Proposition 6.1 progressions. -/

noncomputable section
namespace ArtinMatthews

open Filter OAI OAI.SevenEighths
open scoped ContDiff Topology

def cubicSieveNormalizedScale {J : Type*} [Fintype J] [DecidableEq J] (e : J → ℝ) (x : ℝ) : ℝ :=
  Real.log x / (x * literalMarkedArrayMean e x)

def CubicSieveDivisorWeightedBound {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (Φ : ℝ → ℝ) (ε : ℝ) (m : ℕ) (C : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ᶠ x : ℝ in atTop,
    cubicSieveNormalizedScale e x * cubicSieveDivisorWeightedError e Φ
      (cubicSieveSourceExponent ε m) x m ≤
      C * Real.exp (-(2 * (m : ℝ))) / (cubicSieveSourceExponent ε m) ^ 2 + δ

theorem cubicSieve_actual_rough_bound {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j, 0 < e j ∧ e j ≤ 1 / 5)
    (A : ℤ) (hA : A ≠ 0)
    (hnoncube : ¬ ∃ y : OAI.CubicFirstMoment.Eisenstein,
      y ^ 3 = (A : OAI.CubicFirstMoment.Eisenstein))
    {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) {ε : ℝ} (hε : 0 < ε) (hεq : ε < 1 / 4)
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ) (hΦ₀ : ∀ t, 0 ≤ Φ t) (hΦ₁ : ∀ t, ‖Φ t‖ ≤ 1)
    (hs : Function.support Φ ⊆ Set.Ioo 1 2)
    (hsource : ∃ Cν : ℝ, 0 < Cν ∧ ∀ᶠ x : ℝ in atTop,
      GiantSamplingShiftedBilinearBound (cubicNumeratorHeckeCharacter A hA) Φ x (ε / 1024) Cν)
    (m : ℕ) (C : ℝ) (herror : CubicSieveDivisorWeightedBound e Φ ε m C)
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop,
      cubicSieveNormalizedScale e x *
        ‖markedActualRoughThetaSum e (cubicNumeratorHeckeCharacter A hA) χ
          (giantMarkedCenteredCore ε) Φ 3 (cubicSieveSourceExponent ε m) x‖ ≤
        C * Real.exp (-(2 * (m : ℝ))) / (cubicSieveSourceExponent ε m) ^ 2 + δ := by
  let γ := cubicSieveSourceExponent ε m
  let η := cubicNumeratorHeckeCharacter A hA
  let K := (1 / 2 : ℝ) ^ Fintype.card J
  let d := δ / 2
  have hK : 0 < K := by dsimp only [K]; positivity
  have hd : 0 < d := half_pos hδ
  have hm := literalMarkedArrayMean_lower_eventually e (fun j => (he j).1)
  have hu := cubicSieve_upperTheta_log_saving e he A hA hnoncube χ hε hεq Φ hΦ hΦ₁ hs hsource m 2
  have hc := giantMarkedCenteredCore_interface e (fun j => (he j).2.trans_lt (by norm_num)) hε hεq
  have hL := Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 / (K * d)))
  filter_upwards [hm, hu, hc, hL, herror d hd, eventually_gt_atTop (1 : ℝ)]
    with x hxMean hxUpper hxCore hxL hxErr hx₁
  let W := literalMarkedArrayMean e x
  let L := Real.log x
  let S := cubicSieveNormalizedScale e x
  let H (u : ℕ) : ℂ := (literalMarkedArrayWeight e x u : ℂ)
  let U := cubicSieveUpperThetaSum η χ H Φ ε γ x m
  let R := cubicSieveRoughThetaSum η χ H Φ ε γ x
  let E := cubicSieveDivisorWeightedError e Φ γ x m
  have hx₀ := zero_lt_one.trans hx₁
  have hL₀ : 0 < L := Real.log_pos hx₁
  have hW : 0 < W := hK.trans_le hxMean
  have hS : 0 ≤ S := div_nonneg hL₀.le (mul_pos hx₀ hW).le
  have hUpper : S * ‖U‖ ≤ d := by
    have hnum : 1 ≤ d * (K * L) := by
      have h := (div_le_iff₀ (mul_pos hK hd)).mp hxL
      nlinarith
    calc
      _ ≤ S * (x * L ^ (-2 : ℝ)) := mul_le_mul_of_nonneg_left hxUpper hS
      _ = 1 / (W * L) := by
        change L / (x * W) * (x * L ^ (-2 : ℝ)) = _
        rw [Real.rpow_neg hL₀.le, show L ^ (2 : ℝ) = L ^ (2 : ℕ) from Real.rpow_natCast L 2]
        field_simp [hx₀.ne', hW.ne', hL₀.ne']
      _ ≤ 1 / (K * L) := one_div_le_one_div_of_le (mul_pos hK hL₀)
        (mul_le_mul_of_nonneg_right hxMean hL₀.le)
      _ ≤ _ := (div_le_iff₀ (mul_pos hK hL₀)).mpr hnum
  have hErr : ‖R - U‖ ≤ E :=
    cubicSieve_rough_sub_upper_norm_le e η χ Φ hΦ₀ ε γ x hx₀.le m hxCore.1
  have hR : ‖R‖ ≤ E + ‖U‖ := by
    calc
      _ = ‖(R - U) + U‖ := congrArg norm (sub_add_cancel _ _).symm
      _ ≤ ‖R - U‖ + ‖U‖ := norm_add_le _ _
      _ ≤ _ := add_le_add hErr le_rfl
  rw [← cubicSieve_roughTheta_eq_actual e η χ Φ hs ε γ hx₁.le]
  calc
    _ ≤ S * (E + ‖U‖) := mul_le_mul_of_nonneg_left hR hS
    _ = S * E + S * ‖U‖ := mul_add _ _ _
    _ ≤ (C * Real.exp (-(2 * (m : ℝ))) / γ ^ 2 + d) + d := add_le_add hxErr hUpper
    _ = _ := by dsimp only [d, γ]; ring

end ArtinMatthews
