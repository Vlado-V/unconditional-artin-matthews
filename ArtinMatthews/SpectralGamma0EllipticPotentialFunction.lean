module

public import ArtinMatthews.SpectralGamma0EllipticCoordinates
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! A compact smooth extension of the actual eigenvalue potential λ y⁻².
The cutoff is the same genuine positive-height cutoff as the H¹ pair. -/
noncomputable section
open Set
open scoped ContDiff
namespace ArtinMatthews

def spectralEllipticPotentialSection (lam : ℝ) (z : UpperHalfPlane) : ℂ :=
  ((lam / z.im^2 : ℝ) : ℂ)

theorem spectralEllipticPotentialSection_smooth (lam : ℝ) :
    ContDiffOn ℝ ∞ (fun z : ℂ =>
      spectralEllipticPotentialSection lam (UpperHalfPlane.ofComplex z))
      {z : ℂ | 0 < z.im} := by
  have hreal : ContDiffOn ℝ ∞ (fun z : ℂ => lam / z.im^2)
      {z : ℂ | 0 < z.im} :=
    contDiffOn_const.div (Complex.imCLM.contDiff.contDiffOn.pow 2)
      (fun z hz => pow_ne_zero 2 (ne_of_gt hz))
  apply (Complex.ofRealCLM.contDiff.comp_contDiffOn hreal).congr
  intro z hz
  simp only [spectralEllipticPotentialSection,
    UpperHalfPlane.ofComplex_apply_of_im_pos hz, UpperHalfPlane.mk_im,
    Function.comp_apply, Complex.ofRealCLM_apply]

variable (φ : SchwartzMap (ℝ × ℝ) ℂ) {A a b : ℝ}
  (ha : 0 < a) (hφ : tsupport φ ⊆ spectralPlaneRectangle A a b)

def spectralEllipticPotentialFunction (lam : ℝ) : (Fin 2 → ℝ) → ℝ :=
  spectralEllipticScalar Complex.reCLM
    (spectralCoreLocalization φ ha hφ (spectralEllipticPotentialSection lam)
      (spectralEllipticPotentialSection_smooth lam))

theorem spectralEllipticPotentialFunction_smooth (lam : ℝ) :
    ContDiff ℝ ∞ (spectralEllipticPotentialFunction φ ha hφ lam) :=
  spectralEllipticScalar_contDiff _ _ ((spectralCoreLocalization φ ha hφ
    (spectralEllipticPotentialSection lam)
    (spectralEllipticPotentialSection_smooth lam)).smooth (⊤ : ℕ∞))

theorem spectralEllipticPotentialFunction_compact (lam : ℝ) :
    HasCompactSupport (spectralEllipticPotentialFunction φ ha hφ lam) :=
  spectralEllipticScalar_compact _ _
    (spectralCoreLocalizationFun_hasCompactSupport φ hφ _)

theorem spectralEllipticPotentialFunction_eq (lam : ℝ) {x : Fin 2 → ℝ}
    (hx : 0 < x 1) (hplateau : φ (spectralEllipticCoordinates x) = 1) :
    spectralEllipticPotentialFunction φ ha hφ lam x = lam / (x 1)^2 := by
  have hz : 0 < (Complex.equivRealProdCLM.symm (spectralEllipticCoordinates x)).im := by
    simpa only [spectralEllipticCoordinates_apply, Complex.equivRealProdCLM_symm_apply,
      Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add] using hx
  change (φ (spectralEllipticCoordinates x) *
    spectralEllipticPotentialSection lam (UpperHalfPlane.ofComplex
      (Complex.equivRealProdCLM.symm (spectralEllipticCoordinates x)))).re = _
  rw [hplateau, one_mul]
  unfold spectralEllipticPotentialSection
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz]
  simp only [UpperHalfPlane.mk_im, Complex.ofReal_re, spectralEllipticCoordinates_apply,
    Complex.equivRealProdCLM_symm_apply, Complex.add_im, Complex.ofReal_im,
    Complex.mul_im, Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add]

end ArtinMatthews
