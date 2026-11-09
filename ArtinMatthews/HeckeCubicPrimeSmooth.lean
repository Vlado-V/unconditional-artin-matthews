module

public import ArtinMatthews.HeckePrimeSmoothPower
public import ArtinMatthews.HeckePrimeSmoothSums
public import ArtinMatthews.HeckeDirichletTwistNonprincipal
public import ArtinMatthews.HeckePrimeLogSaving


set_option backward.privateInPublic true
@[expose] public section

/-! Actual smooth long-frequency prime cancellation for the concrete cubic
Hecke theta coefficient, uniform in logarithmic Dirichlet moduli. -/

noncomputable section
namespace ArtinMatthews
open OAI OAI.SevenEighths Filter
open scoped ContDiff Topology

theorem cubicNumeratorPrimeSmooth_power (A : ℤ) (hA : A ≠ 0)
    (hnoncube : ¬ ∃ y : OAI.CubicFirstMoment.Eisenstein,
      y^3 = (A : OAI.CubicFirstMoment.Eisenstein))
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (B : ℝ) (hB : 0 ≤ B) :
    ∃ K H₀ : ℝ, 0 < K ∧ 0 < H₀ ∧ ∀ H : ℝ, H₀ ≤ H →
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      ((heckeDirichletTwist (cubicNumeratorHeckeCharacter A hA) χ).modulus.absNorm : ℝ) ≤ H →
      ∀ t : ℝ, |t| ≤ H^B →
      ‖heckeRationalPrimeSmoothSum (cubicNumeratorHeckeCharacter A hA) χ W H t‖ ≤
        K*H^(29/32 : ℝ) := by
  obtain ⟨K, H₀, hK, _, hpower⟩ := heckePrimePolynomial_smooth_power W a b ha hsupp hW B hB
  obtain ⟨BW, hBW, hprofile⟩ := HeckePrimeAnnular.fixed_profile_norm_bound
    W hW.continuous a b 0 0 ha
  have hWB : ∀ y, ‖W y‖ ≤ BW := by
    intro y
    by_cases hy : W y = 0
    · simpa only [hy, norm_zero] using hBW.le
    · simpa only [neg_zero, Real.rpow_zero, mul_one] using
        hprofile 0 ⟨le_rfl, le_rfl⟩ y (hsupp hy)
  refine ⟨K+3*max 1 b*BW, max H₀ 1, by positivity,
    lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro H hH q _ χ hmod t ht
  have hH1 : 1 ≤ H := (le_max_right _ _).trans hH
  have hp := hpower H ((le_max_left _ _).trans hH) (heckeDirichletTwist _ χ)
    (cubicNumeratorHeckeDirichletTwist_nonprincipal A hA hnoncube χ) hmod t ht
  rw [heckeRationalPrimeSmoothSum_eq_finite _ χ W a b H t (by linarith) hsupp]
  exact heckeRationalPrimeSum_of_polynomial_power _ χ W b H t K BW hH1 hBW.le hWB hp

theorem cubicNumeratorPrimeSmooth_all_log (A : ℤ) (hA : A ≠ 0)
    (hnoncube : ¬ ∃ y : OAI.CubicFirstMoment.Eisenstein,
      y^3 = (A : OAI.CubicFirstMoment.Eisenstein))
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (A₀ B δ D : ℝ) (hB : 0 ≤ B) (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (Real.log x)^A₀ →
      ∀ (χ : DirichletCharacter ℂ q) (H : ℝ), x^δ ≤ H →
      ∀ t : ℝ, |t| ≤ x^B →
      ‖heckeRationalPrimeSmoothSum (cubicNumeratorHeckeCharacter A hA) χ W H t‖ ≤
        H*(Real.log x)^(-D) := by
  obtain ⟨K, H₀, hK, _, hpower⟩ := cubicNumeratorPrimeSmooth_power A hA hnoncube
    W a b ha hsupp hW (B/δ) (div_nonneg hB hδ.le)
  filter_upwards [heckeDirichletTwist_modulus_eventually (cubicNumeratorHeckeCharacter A hA) A₀ δ hδ,
    heckePrime_uniform_power_log_saving K (29/32) δ D hK.le (by norm_num) hδ,
    (tendsto_rpow_atTop hδ).eventually (eventually_ge_atTop H₀),
    eventually_gt_atTop (0 : ℝ)] with x hmod hsave hlarge hx
  intro q _ hq χ H hH t ht
  apply (hpower H (hlarge.trans hH) q χ ((hmod q hq χ).trans hH) t
    (ht.trans (heckePrime_frequency_transport hx hδ hB hH))).trans
  exact hsave H hH

end ArtinMatthews
