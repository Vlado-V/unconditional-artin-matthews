module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Topology.Sheaves.Init
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Echelon.Zsqrtd


set_option backward.privateInPublic true
@[expose] public section

/-! Differential formulas for the radial powers underlying the Newtonian kernel.
All derivatives below are actual real Fréchet derivatives. -/

noncomputable section
open scoped RealInnerProductSpace Topology
namespace OAI.Analysis.PDE.Schauder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def radialPower (p : ℝ) (x : E) : ℝ := (‖x‖ ^ 2) ^ p

def radialPowerGradient (p : ℝ) (x : E) : E →L[ℝ] ℝ :=
  (2 * p * (‖x‖ ^ 2) ^ (p - 1)) • innerSL ℝ x

def realInnerBilinear : E →L[ℝ] E →L[ℝ] ℝ := innerSL ℝ

@[simp] theorem realInnerBilinear_apply (v w : E) :
    realInnerBilinear v w = ⟪v, w⟫ := rfl

def radialPowerHessian (p : ℝ) (x : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  (2 * p * (‖x‖ ^ 2) ^ (p - 1)) • realInnerBilinear +
    (4 * p * (p - 1) * (‖x‖ ^ 2) ^ (p - 2)) •
      (innerSL ℝ x).smulRight (innerSL ℝ x)

theorem contDiffAt_radialPower (p : ℝ) {x : E} (hx : x ≠ 0) :
    ContDiffAt ℝ ⊤ (radialPower p) x :=
  (contDiff_norm_sq ℝ).contDiffAt.rpow_const_of_ne (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))

theorem hasFDerivAt_radialPower (p : ℝ) {x : E} (hx : x ≠ 0) :
    HasFDerivAt (radialPower p) (radialPowerGradient p x) x := by
  have h := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.rpow_const
    (p := p) (Or.inl (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)))
  simp_rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul] at h
  have hc : (p * (‖x‖ ^ 2) ^ (p - 1)) * 2 = 2 * p * (‖x‖ ^ 2) ^ (p - 1) := by ring
  simpa only [radialPower, radialPowerGradient, smul_smul, Nat.cast_ofNat, hc] using! h

theorem radialPowerHessian_apply (p : ℝ) (x v w : E) :
    radialPowerHessian p x v w =
      2 * p * (‖x‖ ^ 2) ^ (p - 1) * ⟪v, w⟫ +
      4 * p * (p - 1) * (‖x‖ ^ 2) ^ (p - 2) * ⟪x, v⟫ * ⟪x, w⟫ := by
  simp [radialPowerHessian, smul_eq_mul, mul_assoc]

theorem hasFDerivAt_radialPowerGradient (p : ℝ) {x : E} (hx : x ≠ 0) :
    HasFDerivAt (radialPowerGradient p) (radialPowerHessian p x) x := by
  have hp := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.rpow_const
    (p := p - 1) (Or.inl (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)))
  simp_rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul] at hp
  have h := (hp.const_mul (2 * p)).smul (realInnerBilinear (E := E)).hasFDerivAt
  convert! h using 1
  ext v w
  change 2 * p * (‖x‖ ^ 2) ^ (p - 1) * ⟪v, w⟫ +
      4 * p * (p - 1) * (‖x‖ ^ 2) ^ (p - 2) * (⟪x, v⟫ * ⟪x, w⟫) =
    2 * p * (‖x‖ ^ 2) ^ (p - 1) * ⟪v, w⟫ +
      (2 * p * (((p - 1) * (‖x‖ ^ 2) ^ (p - 1 - 1) * 2) * ⟪x, v⟫)) * ⟪x, w⟫
  rw [show p - 1 - 1 = p - 2 by ring]
  ring

theorem fderiv_radialPower (p : ℝ) {x : E} (hx : x ≠ 0) :
    fderiv ℝ (radialPower p) x = radialPowerGradient p x :=
  (hasFDerivAt_radialPower p hx).fderiv

theorem second_fderiv_radialPower (p : ℝ) {x : E} (hx : x ≠ 0) :
    fderiv ℝ (fderiv ℝ (radialPower p)) x = radialPowerHessian p x := by
  have hne : ∀ᶠ y in 𝓝 x, y ≠ (0 : E) := (isOpen_compl_singleton.mem_nhds hx)
  have he : fderiv ℝ (radialPower p) =ᶠ[𝓝 x] radialPowerGradient p :=
    hne.mono fun y hy => fderiv_radialPower p hy
  rw [he.fderiv_eq]
  exact (hasFDerivAt_radialPowerGradient p hx).fderiv

end OAI.Analysis.PDE.Schauder
