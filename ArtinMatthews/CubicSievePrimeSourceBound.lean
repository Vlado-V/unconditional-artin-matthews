module

public import ArtinMatthews.CubicSievePrimeBoundWithExtraction
public import ArtinMatthews.CubicSieveDivisorWeightedActual
public import ArtinMatthews.MarkedCorrelationNormalization


set_option backward.privateInPublic true
@[expose] public section

/-! The literal marked cubic prime estimate uses the proved Section 7
weighted bound. Its only analytic input is the actual Proposition 5.1 test. -/

noncomputable section
namespace ArtinMatthews

open Filter OAI OAI.SevenEighths
open scoped ContDiff Topology Asymptotics

theorem cubicSieve_actual_marked_prime_source_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (J : Type) [Fintype J] [DecidableEq J]
      (e : J → ℝ), Function.Injective e →
      (∀ j, (1 / 10 : ℝ) < e j ∧ e j < 1 / 5) →
      ∀ (A : ℤ) (hA : A ≠ 0),
      (¬ ∃ y : OAI.CubicFirstMoment.Eisenstein, y ^ 3 = (A : OAI.CubicFirstMoment.Eisenstein)) →
      ∀ (M : ℕ) [NeZero M] (χ : DirichletCharacter ℂ M)
      (ε : ℝ), 0 < ε → ε < 1 / 4 →
      ∀ (Φ : ℝ → ℝ), ContDiff ℝ ∞ Φ → (∀ t, 0 ≤ Φ t) → (∀ t, ‖Φ t‖ ≤ 1) →
      Function.support Φ ⊆ Set.Ioo 1 2 →
      100 * (5 * (30 : ℝ) + 36) < (Fintype.card J : ℝ) →
      (∃ Cν : ℝ, 0 < Cν ∧ ∀ᶠ x : ℝ in atTop,
        GiantSamplingShiftedBilinearBound (cubicNumeratorHeckeCharacter A hA) Φ x (ε / 1024) Cν) →
      ∀ m : ℕ, 1 ≤ m → ∀ δ : ℝ, 0 < δ → ∀ᶠ x : ℝ in atTop,
        cubicSieveNormalizedScale e x *
          ‖markedActualPrimeThetaSum e (cubicNumeratorHeckeCharacter A hA) χ
            (giantMarkedCenteredCore ε) Φ 3 x‖ ≤
          C * Real.exp (-(2 * (m : ℝ))) / (cubicSieveSourceExponent ε m) ^ 2 + δ := by
  obtain ⟨C, hC, hweighted⟩ := cubicSieve_actual_divisorWeighted_bound_finite.{0}
  refine ⟨C, hC, ?_⟩
  intro J instF instD e hinj he A hA hnoncube M instM χ ε hε hεq Φ hΦ hΦ₀ hΦ₁ hs hdepth hsource m hm δ hδ
  have he' (j : J) : 0 < e j ∧ e j ≤ 1 / 5 :=
    ⟨(by norm_num : (0 : ℝ) < 1 / 10).trans (he j).1, (he j).2.le⟩
  have herror := hweighted J e he' hinj Φ hΦ (fun t => by simpa only [Real.norm_eq_abs] using hΦ₁ t)
    hs ε hε hεq m hm
  exact cubicSieve_actual_marked_prime_bound_with_extraction e hinj he A hA hnoncube χ
    hε hεq Φ hΦ hΦ₀ hΦ₁ hs hdepth hsource m C herror δ hδ

theorem cubicSieve_actual_marked_prime_source_normalized {J : Type} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (hinj : Function.Injective e)
    (he : ∀ j, (1 / 10 : ℝ) < e j ∧ e j < 1 / 5)
    (A : ℤ) (hA : A ≠ 0)
    (hnoncube : ¬ ∃ y : OAI.CubicFirstMoment.Eisenstein, y ^ 3 = (A : OAI.CubicFirstMoment.Eisenstein))
    {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M)
    {ε : ℝ} (hε : 0 < ε) (hεq : ε < 1 / 4)
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ) (hΦ₀ : ∀ t, 0 ≤ Φ t) (hΦ₁ : ∀ t, ‖Φ t‖ ≤ 1)
    (hs : Function.support Φ ⊆ Set.Ioo 1 2)
    (hdepth : 100 * (5 * (30 : ℝ) + 36) < (Fintype.card J : ℝ))
    (hsource : ∃ Cν : ℝ, 0 < Cν ∧ ∀ᶠ x : ℝ in atTop,
      GiantSamplingShiftedBilinearBound (cubicNumeratorHeckeCharacter A hA) Φ x (ε / 1024) Cν) :
    Tendsto (fun x : ℝ => cubicSieveNormalizedScale e x *
      ‖markedActualPrimeThetaSum e (cubicNumeratorHeckeCharacter A hA) χ
        (giantMarkedCenteredCore ε) Φ 3 x‖) atTop (𝓝 0) := by
  obtain ⟨C, _, hbound⟩ := cubicSieve_actual_marked_prime_source_bound
  have hnonneg : ∀ᶠ x : ℝ in atTop, 0 ≤ cubicSieveNormalizedScale e x := by
    filter_upwards [literalMarkedArrayMean_lower_eventually e
      (fun j => (by norm_num : (0 : ℝ) < 1 / 10).trans (he j).1),
      eventually_gt_atTop (1 : ℝ)] with x hxMean hx
    unfold cubicSieveNormalizedScale
    exact div_nonneg (Real.log_pos hx).le
      (mul_nonneg (zero_lt_one.trans hx).le
        ((by positivity : (0 : ℝ) < (1 / 2 : ℝ) ^ Fintype.card J).le.trans hxMean))
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards [hnonneg] with x hx
    exact ha.trans_le (mul_nonneg hx (norm_nonneg _))
  · intro a ha
    have ht := marked_correlation_even_sieve_error_tendsto (ε / 64) C
    change Tendsto (fun n : ℕ => C * Real.exp (-(2 * (n : ℝ))) /
      (cubicSieveSourceExponent ε n) ^ 2) atTop (𝓝 0) at ht
    obtain ⟨m, hmSmall, hm⟩ := ((ht.eventually (gt_mem_nhds (half_pos ha))).and
      (eventually_ge_atTop (1 : ℕ))).exists
    filter_upwards [hbound J e hinj he A hA hnoncube M χ ε hε hεq Φ hΦ hΦ₀ hΦ₁
      hs hdepth hsource m hm (a / 2) (half_pos ha)] with x hx
    linarith

theorem cubicSieve_actual_marked_prime_source_norm {J : Type} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (hinj : Function.Injective e)
    (he : ∀ j, (1 / 10 : ℝ) < e j ∧ e j < 1 / 5)
    (A : ℤ) (hA : A ≠ 0)
    (hnoncube : ¬ ∃ y : OAI.CubicFirstMoment.Eisenstein, y ^ 3 = (A : OAI.CubicFirstMoment.Eisenstein))
    {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M)
    {ε : ℝ} (hε : 0 < ε) (hεq : ε < 1 / 4)
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ) (hΦ₀ : ∀ t, 0 ≤ Φ t) (hΦ₁ : ∀ t, ‖Φ t‖ ≤ 1)
    (hs : Function.support Φ ⊆ Set.Ioo 1 2)
    (hdepth : 100 * (5 * (30 : ℝ) + 36) < (Fintype.card J : ℝ))
    (hsource : ∃ Cν : ℝ, 0 < Cν ∧ ∀ᶠ x : ℝ in atTop,
      GiantSamplingShiftedBilinearBound (cubicNumeratorHeckeCharacter A hA) Φ x (ε / 1024) Cν) :
    Tendsto (fun x : ℝ => Real.log x / x *
      ‖markedActualPrimeThetaSum e (cubicNumeratorHeckeCharacter A hA) χ
        (giantMarkedCenteredCore ε) Φ 3 x‖) atTop (𝓝 0) := by
  let K : ℝ := (1 / (Real.log 2 / 2)) ^ Fintype.card J
  have ht := (cubicSieve_actual_marked_prime_source_normalized e hinj he A hA hnoncube χ
    hε hεq Φ hΦ hΦ₀ hΦ₁ hs hdepth hsource).const_mul K
  simp only [mul_zero] at ht
  apply squeeze_zero' _ _ ht
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact mul_nonneg (div_nonneg (Real.log_pos hx).le (zero_lt_one.trans hx).le) (norm_nonneg _)
  · filter_upwards [marked_array_moment_bounds_eventually e
      (fun j => (by norm_num : (0 : ℝ) < 1 / 10).trans (he j).1),
      eventually_gt_atTop (1 : ℝ)] with x hxMean hx
    have hW : 0 < literalMarkedArrayMean e x :=
      (by positivity : (0 : ℝ) < (1 / 2 : ℝ) ^ Fintype.card J).trans_le hxMean.1
    have hscale : 0 ≤ cubicSieveNormalizedScale e x :=
      div_nonneg (Real.log_pos hx).le (mul_pos (zero_lt_one.trans hx) hW).le
    calc
      _ = literalMarkedArrayMean e x * (cubicSieveNormalizedScale e x *
          ‖markedActualPrimeThetaSum e (cubicNumeratorHeckeCharacter A hA) χ
            (giantMarkedCenteredCore ε) Φ 3 x‖) := by
        unfold cubicSieveNormalizedScale
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hxMean.2.1 (mul_nonneg hscale (norm_nonneg _))

theorem cubicSieve_actual_marked_prime_source_isLittleO {J : Type} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (hinj : Function.Injective e)
    (he : ∀ j, (1 / 10 : ℝ) < e j ∧ e j < 1 / 5)
    (A : ℤ) (hA : A ≠ 0)
    (hnoncube : ¬ ∃ y : OAI.CubicFirstMoment.Eisenstein, y ^ 3 = (A : OAI.CubicFirstMoment.Eisenstein))
    {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M)
    {ε : ℝ} (hε : 0 < ε) (hεq : ε < 1 / 4)
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ) (hΦ₀ : ∀ t, 0 ≤ Φ t) (hΦ₁ : ∀ t, ‖Φ t‖ ≤ 1)
    (hs : Function.support Φ ⊆ Set.Ioo 1 2)
    (hdepth : 100 * (5 * (30 : ℝ) + 36) < (Fintype.card J : ℝ))
    (hsource : ∃ Cν : ℝ, 0 < Cν ∧ ∀ᶠ x : ℝ in atTop,
      GiantSamplingShiftedBilinearBound (cubicNumeratorHeckeCharacter A hA) Φ x (ε / 1024) Cν) :
    (fun x => markedActualPrimeThetaSum e (cubicNumeratorHeckeCharacter A hA) χ
      (giantMarkedCenteredCore ε) Φ 3 x) =o[atTop] (fun x : ℝ => x / Real.log x) :=
  marked_correlation_isLittleO_of_normalized_norm _
    (cubicSieve_actual_marked_prime_source_norm e hinj he A hA hnoncube χ hε hεq Φ hΦ hΦ₀ hΦ₁ hs hdepth hsource)

end ArtinMatthews
