module

public import ArtinMatthews.ProbeIdealGaussPhase
public import ArtinMatthews.ProbeIdealSourceWeight
public import ArtinMatthews.ProbeIdealGaussValues
public import ArtinMatthews.ProbeIdealSourceEuler
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Actual all-prime source correction on both enlarged manuscript regions. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField IsDedekindDomain
open scoped NumberField BigOperators Classical
noncomputable section

variable (K : Type*) [Field K] [NumberField K]

theorem probeIdealPrime_norm_gt_one (P : HeightOneSpectrum (𝓞 K)) :
    1 < (Ideal.absNorm P.asIdeal : ℝ) := by
  have h0 : Ideal.absNorm P.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr P.ne_bot
  have h1 : Ideal.absNorm P.asIdeal ≠ 1 := Ideal.absNorm_eq_one_iff.not.mpr P.isPrime.ne_top
  exact_mod_cast (show 1 < Ideal.absNorm P.asIdeal by omega)

theorem probeIdealGaussLocalLambda_norm (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (hχ : orderOf χ = 6) :
    ‖probeIdealGaussLocalLambda K P χ‖ = 1 := by
  have hn : χ ^ 2 ≠ 1 := by
    intro he
    have hd := (orderOf_dvd_iff_pow_eq_one).mpr he
    rw [hχ] at hd
    norm_num at hd
  have hq : 0 < (Ideal.absNorm P.asIdeal : ℝ) :=
    lt_trans zero_lt_one (probeIdealPrime_norm_gt_one K P)
  rw [probeIdealGaussLocalLambda, norm_neg, norm_pow, probeIdealGaussGamma,
    norm_div, probeIdealTau_norm K P _ hn, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), div_self (Real.sqrt_ne_zero'.mpr hq), one_pow]

omit [NumberField K] in
theorem probeIdealCharacter_unit_sixth (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (hχ : orderOf χ = 6)
    (u : ((𝓞 K) ⧸ P.asIdeal)ˣ) : (χ u) ^ 6 = 1 := by
  rw [← χ.pow_apply_coe,
    (orderOf_dvd_iff_pow_eq_one).mp (by rw [hχ]), MulChar.one_apply_coe]

omit [NumberField K] in
theorem probeIdealCharacter_unit_norm (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (hχ : orderOf χ = 6)
    (u : ((𝓞 K) ⧸ P.asIdeal)ˣ) : ‖χ u‖ = 1 := by
  apply (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by decide : 6 ≠ 0)).mp
  rw [← norm_pow, probeIdealCharacter_unit_sixth K P χ hχ u, norm_one]

private theorem probeIdealRegion_parameters (P : HeightOneSpectrum (𝓞 K))
    (c ξ w z : ℂ) (hc : ‖c‖ ≤ 1)
    (hregion : ArtinMatthews.probeEulerRegion ξ.re w.re z.re) :
    ‖ArtinMatthews.probeLocalV (Ideal.absNorm P.asIdeal) z‖ < 1 ∧
      ‖(Ideal.absNorm P.asIdeal : ℂ) ^ (-w)‖ < 1 ∧
      ‖ArtinMatthews.probeLocalE (Ideal.absNorm P.asIdeal) c ξ z‖ < 1 := by
  have hQ := probeIdealPrime_norm_gt_one K P
  have hQ0 := lt_trans zero_lt_one hQ
  obtain ⟨_, hw, hv, he⟩ := ArtinMatthews.probeEulerRegion_individual hregion
  constructor
  · rw [ArtinMatthews.probeLocalV_norm _ hQ0]
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ (by linarith)
  constructor
  · have hh : ‖((Ideal.absNorm P.asIdeal : ℝ) : ℂ) ^ (-w)‖ < 1 := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hQ0, Complex.neg_re]
      exact Real.rpow_lt_one_of_one_lt_of_neg hQ (by linarith)
    simpa only [Complex.ofReal_natCast] using hh
  · exact (ArtinMatthews.probeLocalE_norm_le _ hQ0 c ξ z hc).trans_lt
      (Real.rpow_lt_one_of_one_lt_of_neg hQ (by linarith))

theorem probeIdealGoodSourceSeries_regions (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (hchar : ringChar ((𝓞 K) ⧸ P.asIdeal) ≠ 2)
    (η : ℂ) (hη : η ^ 6 = 1) (u : ((𝓞 K) ⧸ P.asIdeal)ˣ) (ξ w z : ℂ)
    (hregion : ArtinMatthews.probeEulerRegion ξ.re w.re z.re) :
    let Q : ℝ := Ideal.absNorm P.asIdeal
    let Λ := star (probeIdealGaussLocalLambda K P χ) ^ 6
    (1 - ArtinMatthews.probeLocalV Q z) * (1 - ArtinMatthews.probeLocalW Q (χ u) w) /
      (1 - ArtinMatthews.probeLocalD Q (η * (χ u)⁻¹) ξ) *
      probeIdealSourceSeries K P χ 0 (probeIdealGaussGamma K P χ 2)
        (probeIdealGaussLocalVartheta K P χ η) (χ u) ξ w z =
      ArtinMatthews.probeGoodPrimeCorrection Q (χ u) (η * (χ u)⁻¹) Λ ξ w z := by
  have hc : ‖star (probeIdealGaussLocalLambda K P χ) ^ 6‖ ≤ 1 := by
    rw [norm_pow, norm_star, probeIdealGaussLocalLambda_norm K P χ hχ, one_pow]
  obtain ⟨hV, hW, hE⟩ := probeIdealRegion_parameters K P
    (star (probeIdealGaussLocalLambda K P χ) ^ 6) ξ w z hc hregion
  exact probeIdealGoodSourceSeries_cubic_atUnit K P χ hχ hminus hchar η hη u ξ w z hV hW hE

theorem probeIdealGoodSourceSeries_regions_bound (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (hchar : ringChar ((𝓞 K) ⧸ P.asIdeal) ≠ 2)
    (η : ℂ) (hη : η ^ 6 = 1) (u : ((𝓞 K) ⧸ P.asIdeal)ˣ) (ξ w z : ℂ)
    (hregion : ArtinMatthews.probeEulerRegion ξ.re w.re z.re)
    (hcut : (ArtinMatthews.probeEulerCutoff : ℝ) ≤ Ideal.absNorm P.asIdeal) :
    let Q : ℝ := Ideal.absNorm P.asIdeal
    ‖(1 - ArtinMatthews.probeLocalV Q z) * (1 - ArtinMatthews.probeLocalW Q (χ u) w) /
      (1 - ArtinMatthews.probeLocalD Q (η * (χ u)⁻¹) ξ) *
      probeIdealSourceSeries K P χ 0 (probeIdealGaussGamma K P χ 2)
        (probeIdealGaussLocalVartheta K P χ η) (χ u) ξ w z - 1‖ ≤
      160 * Q ^ (-(1 + 1 / 4000 : ℝ)) := by
  dsimp only
  rw [probeIdealGoodSourceSeries_regions K P χ hχ hminus hchar η hη u ξ w z hregion]
  have hηn : ‖η‖ = 1 := by
    apply (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by decide : 6 ≠ 0)).mp
    rw [← norm_pow, hη, norm_one]
  have ha : ‖χ u‖ ≤ 1 := (probeIdealCharacter_unit_norm K P χ hχ u).le
  have hb : ‖η * (χ u)⁻¹‖ ≤ 1 := by
    rw [norm_mul, norm_inv, hηn, probeIdealCharacter_unit_norm K P χ hχ u, inv_one, one_mul]
  have hc : ‖star (probeIdealGaussLocalLambda K P χ) ^ 6‖ ≤ 1 := by
    rw [norm_pow, norm_star, probeIdealGaussLocalLambda_norm K P χ hχ, one_pow]
  obtain ⟨hQ, hs, _⟩ := ArtinMatthews.probeEulerCutoff_spec hcut
  exact ArtinMatthews.probeGoodPrimeCorrection_norm_sub_one_le _ hQ hs _ _ _ _ _ _
    ha hb hc hregion

end

end ArtinMatthews.VaryingKummerAnalytic
