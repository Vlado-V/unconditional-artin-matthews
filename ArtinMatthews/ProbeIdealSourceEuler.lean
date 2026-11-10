module

public import ArtinMatthews.ProbeGoodBadSourceBridge
public import ArtinMatthews.ProbeIdealRawSeries
public import ArtinMatthews.ProbeIdealSourceWeight
public import ArtinMatthews.ProbeIdealPhasePowers
public import ArtinMatthews.ProbeIdealRawAnalyticFactor
public import ArtinMatthews.ProbeIdealRawEuler
public import ArtinMatthews.ProbeIdealSourceBridge
public import ArtinMatthews.ProbePrimeRawAnalyticFactor
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
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The j=0 case of the exact source term shared with the bad-prime proof. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField IsDedekindDomain
open scoped NumberField BigOperators Classical
noncomputable section

variable (K : Type*) [Field K] [NumberField K]

theorem probeIdealGoodSourceSeries_eq_raw (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (η θ ξ w z : ℂ) :
    let Q : ℝ := Ideal.absNorm (P.asIdeal)
    Summable (probeIdealRawTerm K P χ η θ ((Q : ℂ) ^ (-ξ)) ((Q : ℂ) ^ (-w))
      (ArtinMatthews.probeLocalV Q z)) →
    probeIdealSourceSeries K P χ 0 (probeIdealGaussGamma K P χ 2)
      (probeIdealGaussLocalVartheta K P χ η) θ ξ w z =
      probeIdealRawLocalSeries K P χ η θ ((Q : ℂ) ^ (-ξ)) ((Q : ℂ) ^ (-w))
        (ArtinMatthews.probeLocalV Q z) := by
  dsimp only
  intro hs
  simp only [Complex.ofReal_natCast] at hs ⊢
  let f := probeIdealRawTerm K P χ η θ
    ((Ideal.absNorm (P.asIdeal) : ℂ) ^ (-ξ))
    ((Ideal.absNorm (P.asIdeal) : ℂ) ^ (-w))
    (ArtinMatthews.probeLocalV (Ideal.absNorm (P.asIdeal)) z)
  let g : (Fin 2 × ℕ × ℕ × ℕ) → ℂ := fun i =>
    probeIdealSourceTerm K P χ 0 (probeIdealGaussGamma K P χ 2)
      (probeIdealGaussLocalVartheta K P χ η) θ ξ w z i.1 i.2.2.1 i.2.1 i.2.2.2
  have hg (i : Fin 2 × ℕ × ℕ × ℕ) : g i = f (probeSourceIndexEquiv i) := by
    rcases i with ⟨e, k, l, m⟩
    have he := probeIdealRawTerm_eq_source K P χ η θ ξ w z
      (probeBoolFinTwo.symm e) l k m
    simpa only [probeSourceIndexEquiv, Equiv.coe_fn_mk, Equiv.apply_symm_apply,
      Complex.ofReal_natCast, g, f] using he.symm
  have hgfun : g = f ∘ probeSourceIndexEquiv := funext hg
  have hgs : Summable g := by
    rw [hgfun]
    exact hs.comp_injective probeSourceIndexEquiv.injective
  have hsum : (∑' i, g i) = ∑' i, f i := by
    rw [hgfun]
    exact probeSourceIndexEquiv.tsum_eq f
  unfold probeIdealSourceSeries probeIdealRawLocalSeries
  rw [← tsum_fintype (L := SummationFilter.unconditional (Fin 2))]
  exact hgs.tsum_prod.symm.trans hsum

theorem probeIdealGoodSourceSeries_eq_factor (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (hchar : ringChar ((𝓞 K) ⧸ P.asIdeal) ≠ 2)
    (η θ ξ w z : ℂ) (hθ : θ ^ 6 = 1) :
    let Q : ℝ := Ideal.absNorm (P.asIdeal)
    let v := probeIdealGaussLocalVartheta K P χ η
    ‖ArtinMatthews.probeLocalV Q z‖ < 1 →
    ‖ArtinMatthews.probeLocalW Q θ w‖ < 1 →
    ‖ArtinMatthews.probeLocalE Q (v ^ 6) ξ z‖ < 1 →
    probeIdealSourceSeries K P χ 0 (probeIdealGaussGamma K P χ 2)
      v θ ξ w z =
      ArtinMatthews.probeGoodLocalFactor (Q : ℂ)
        (ArtinMatthews.probeLocalV Q z) (ArtinMatthews.probeLocalW Q θ w)
        (ArtinMatthews.probeLocalD Q (η * θ⁻¹) ξ)
        (ArtinMatthews.probeLocalE Q (v ^ 6) ξ z) := by
  dsimp only
  intro hV hW hE
  have hq : (Ideal.absNorm (P.asIdeal) : ℂ) ≠ 0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr
      P.ne_bot
  have he : (probeIdealGaussLocalVartheta K P χ η) ^ 6 *
      (Ideal.absNorm (P.asIdeal) : ℂ) ^ 4 *
      ((Ideal.absNorm (P.asIdeal) : ℂ) ^ (-ξ)) ^ 6 *
      ArtinMatthews.probeLocalV (Ideal.absNorm (P.asIdeal)) z =
      ArtinMatthews.probeLocalE (Ideal.absNorm (P.asIdeal))
        ((probeIdealGaussLocalVartheta K P χ η) ^ 6) ξ z := by
    simp only [ArtinMatthews.probeLocalV, ArtinMatthews.probeLocalE, Complex.ofReal_natCast]
    rw [mul_assoc, mul_assoc]
    congr 1
    simpa only [mul_assoc] using probe_cpow_local_geometric _ hq ξ z
  have hs := (probeIdealRawLocal_hasSum K P χ hχ hminus hchar η θ
    ((Ideal.absNorm (P.asIdeal) : ℂ) ^ (-ξ))
    ((Ideal.absNorm (P.asIdeal) : ℂ) ^ (-w))
    (ArtinMatthews.probeLocalV (Ideal.absNorm (P.asIdeal)) z) hθ hV hW (he.symm ▸ hE)).summable
  rw [probeIdealGoodSourceSeries_eq_raw K P χ η θ ξ w z hs]
  exact probeIdealRawLocal_analytic_factor K P χ hχ hminus hchar η θ ξ w z hθ hV hW hE

theorem probeIdealGoodSourceSeries_correction (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (hchar : ringChar ((𝓞 K) ⧸ P.asIdeal) ≠ 2)
    (η θ ξ w z : ℂ) (hθ : θ ^ 6 = 1) :
    let Q : ℝ := Ideal.absNorm (P.asIdeal)
    let v := probeIdealGaussLocalVartheta K P χ η
    ‖ArtinMatthews.probeLocalV Q z‖ < 1 →
    ‖ArtinMatthews.probeLocalW Q θ w‖ < 1 →
    ‖ArtinMatthews.probeLocalE Q (v ^ 6) ξ z‖ < 1 →
    (1 - ArtinMatthews.probeLocalV Q z) * (1 - ArtinMatthews.probeLocalW Q θ w) /
      (1 - ArtinMatthews.probeLocalD Q (η * θ⁻¹) ξ) *
      probeIdealSourceSeries K P χ 0 (probeIdealGaussGamma K P χ 2)
        v θ ξ w z =
      ArtinMatthews.probeGoodPrimeCorrection Q θ (η * θ⁻¹) (v ^ 6) ξ w z := by
  dsimp only
  intro hV hW hE
  rw [probeIdealGoodSourceSeries_eq_factor K P χ hχ hminus hchar η θ ξ w z hθ hV hW hE]
  rfl


theorem probeIdealGoodSourceSeries_cubic_correction (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (hchar : ringChar ((𝓞 K) ⧸ P.asIdeal) ≠ 2)
    (η θ ξ w z : ℂ) (hη : η ^ 6 = 1) (hθ : θ ^ 6 = 1) :
    let Q : ℝ := Ideal.absNorm P.asIdeal
    let Λ := star (probeIdealGaussLocalLambda K P χ) ^ 6
    ‖ArtinMatthews.probeLocalV Q z‖ < 1 →
    ‖ArtinMatthews.probeLocalW Q θ w‖ < 1 →
    ‖ArtinMatthews.probeLocalE Q Λ ξ z‖ < 1 →
    (1 - ArtinMatthews.probeLocalV Q z) * (1 - ArtinMatthews.probeLocalW Q θ w) /
      (1 - ArtinMatthews.probeLocalD Q (η * θ⁻¹) ξ) *
      probeIdealSourceSeries K P χ 0 (probeIdealGaussGamma K P χ 2)
        (probeIdealGaussLocalVartheta K P χ η) θ ξ w z =
      ArtinMatthews.probeGoodPrimeCorrection Q θ (η * θ⁻¹) Λ ξ w z := by
  dsimp only
  rw [← probeIdealGauss_vartheta_sixth_of_eta K P χ hχ hminus hchar η hη]
  exact probeIdealGoodSourceSeries_correction K P χ hχ hminus hchar η θ ξ w z hθ


theorem probeIdealGoodSourceSeries_cubic_atUnit (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (hchar : ringChar ((𝓞 K) ⧸ P.asIdeal) ≠ 2)
    (η : ℂ) (hη : η ^ 6 = 1) (u : ((𝓞 K) ⧸ P.asIdeal)ˣ) (ξ w z : ℂ) :
    let Q : ℝ := Ideal.absNorm P.asIdeal
    let Λ := star (probeIdealGaussLocalLambda K P χ) ^ 6
    ‖ArtinMatthews.probeLocalV Q z‖ < 1 →
    ‖(Q : ℂ) ^ (-w)‖ < 1 →
    ‖ArtinMatthews.probeLocalE Q Λ ξ z‖ < 1 →
    (1 - ArtinMatthews.probeLocalV Q z) * (1 - ArtinMatthews.probeLocalW Q (χ u) w) /
      (1 - ArtinMatthews.probeLocalD Q (η * (χ u)⁻¹) ξ) *
      probeIdealSourceSeries K P χ 0 (probeIdealGaussGamma K P χ 2)
        (probeIdealGaussLocalVartheta K P χ η) (χ u) ξ w z =
      ArtinMatthews.probeGoodPrimeCorrection Q (χ u) (η * (χ u)⁻¹) Λ ξ w z := by
  dsimp only
  intro hV hW hE
  have h6 : χ ^ 6 = 1 := (orderOf_dvd_iff_pow_eq_one).mp (by rw [hχ])
  have hθ : (χ u) ^ 6 = 1 := by
    rw [← χ.pow_apply_coe, h6, MulChar.one_apply_coe]
  have hnorm : ‖χ u‖ = 1 := by
    apply (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by decide : 6 ≠ 0)).mp
    rw [← norm_pow, hθ, norm_one]
  apply probeIdealGoodSourceSeries_cubic_correction K P χ hχ hminus hchar
    η (χ u) ξ w z hη hθ hV _ hE
  simpa only [ArtinMatthews.probeLocalW, Complex.ofReal_natCast, norm_mul,
    hnorm, one_mul] using hW

end

end ArtinMatthews.VaryingKummerAnalytic
