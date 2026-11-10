module

public import ArtinMatthews.ProbeIdealGaussPhase
public import ArtinMatthews.ProbeSexticGaussPhase
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
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The sixth power used by the good Euler factor has no quadratic phase. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField IsDedekindDomain OAI.SevenEighths
open scoped BigOperators Classical NumberField
noncomputable section

variable {F : Type*} [Field F] [Fintype F]

theorem probeSexticGauss_gamma_three_sq (χ : MulChar F ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) :
    probeGaussGamma χ ψ 3 ^ 2 = 1 := by
  have h6 : χ ^ 6 = 1 := by rw [← orderOf_dvd_iff_pow_eq_one, hχ]
  have hn : χ ^ 3 ≠ 1 := by
    intro he
    have hd := (orderOf_dvd_iff_pow_eq_one).mpr he
    rw [hχ] at hd
    norm_num at hd
  have hi : (χ ^ 3)⁻¹ = χ ^ 3 := by
    apply (mul_left_inj (χ ^ 3)).mp
    rw [inv_mul_cancel, ← pow_add]
    exact h6.symm
  have hm : (χ ^ 3) (-1) = 1 := by
    rw [χ.pow_apply' (by decide : 3 ≠ 0), hminus, one_pow]
  have hg : gaussSum (χ ^ 3) ψ ^ 2 = (Fintype.card F : ℂ) := by
    simpa only [hi, hm, one_mul, ← pow_two] using
      ProbeGauss.gauss_inverse_pair (χ ^ 3) ψ hn hψ
  have hs : (Real.sqrt (Fintype.card F) : ℂ) ^ 2 = (Fintype.card F : ℂ) := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg (Fintype.card F) : (0 : ℝ) ≤ _)
  have hq : (Fintype.card F : ℂ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Fintype.card_pos (α := F))
  rw [probeGaussGamma, ProbeGauss.normalizedGauss, div_pow, hg, hs, div_self hq]

theorem probeSexticGauss_G_sixth (χ : MulChar F ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (hchar : ringChar F ≠ 2) : probeGaussLocalG χ ψ ^ 6 = 1 := by
  have h4 : (4 : F) ≠ 0 := by
    have h2 := Ring.two_ne_zero hchar
    convert pow_ne_zero 2 h2 using 1
    norm_num
  have h46 : χ (4 : F) ^ 6 = 1 := by
    rw [← χ.pow_apply' (by decide : 6 ≠ 0),
      (orderOf_dvd_iff_pow_eq_one).mp (by rw [hχ]),
      MulChar.one_apply (isUnit_iff_ne_zero.mpr h4)]
  have hg6 : probeGaussGamma χ ψ 3 ^ 6 = 1 := by
    rw [show 6 = 2 * 3 by decide, pow_mul,
      probeSexticGauss_gamma_three_sq χ hχ hminus ψ hψ, one_pow]
  rw [probeGaussLocalG, mul_pow, inv_pow, h46, inv_one, one_mul, hg6]

theorem probeSexticGauss_vartheta_sixth (χ : MulChar F ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (hchar : ringChar F ≠ 2) (η : ℂ) :
    probeGaussLocalVartheta χ ψ η ^ 6 = star (probeGaussLocalLambda χ ψ) ^ 6 * η ^ 6 := by
  have hG : star (probeGaussLocalG χ ψ) ^ 6 = 1 := by
    rw [← star_pow, probeSexticGauss_G_sixth χ hχ hminus ψ hψ hchar, star_one]
  rw [probeGaussLocalVartheta, mul_pow, mul_pow, hG, mul_one]

variable (K : Type*) [Field K] [NumberField K]

theorem probeIdealGauss_vartheta_sixth (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (hchar : ringChar ((𝓞 K) ⧸ P.asIdeal) ≠ 2) (η : ℂ) :
    probeIdealGaussLocalVartheta K P χ η ^ 6 =
      star (probeIdealGaussLocalLambda K P χ) ^ 6 * η ^ 6 := by
  let : Field ((𝓞 K) ⧸ P.asIdeal) := Ideal.Quotient.field _
  let : Finite ((𝓞 K) ⧸ P.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient P.ne_bot
  let : Fintype ((𝓞 K) ⧸ P.asIdeal) := Fintype.ofFinite _
  have hc : Fintype.card ((𝓞 K) ⧸ P.asIdeal) = Ideal.absNorm P.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have hγ (j : ℕ) : probeIdealGaussGamma K P χ j =
      probeGaussGamma χ (probeIdealResiduePhase K P) j := by
    simp only [probeIdealGaussGamma, probeIdealTau, tsum_fintype,
      probeGaussGamma, ProbeGauss.normalizedGauss, gaussSum, hc]
  have he := probeSexticGauss_vartheta_sixth χ hχ hminus
    (probeIdealResiduePhase K P) (probeIdealResiduePhase_primitive K P) hchar η
  simpa only [probeIdealGaussLocalVartheta, probeIdealGaussLocalLambda,
    probeIdealGaussLocalG, probeGaussLocalVartheta, probeGaussLocalLambda,
    probeGaussLocalG, hγ, map_ofNat] using he

theorem probeIdealGauss_vartheta_sixth_of_eta (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (hchar : ringChar ((𝓞 K) ⧸ P.asIdeal) ≠ 2)
    (η : ℂ) (hη : η ^ 6 = 1) :
    probeIdealGaussLocalVartheta K P χ η ^ 6 =
      star (probeIdealGaussLocalLambda K P χ) ^ 6 := by
  rw [probeIdealGauss_vartheta_sixth K P χ hχ hminus hchar η, hη, mul_one]

end

end ArtinMatthews.VaryingKummerAnalytic
