module

public import ArtinMatthews.SourceArchSphericalSection
public import OAI.NumberTheory.DirichletL.MeanSquare.UnitRows
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

/-! The spherical section in upper-halfspace coordinates, with the existing positive Laplacian. -/
namespace ArtinMatthews.SourceArchJacquet
open Matrix OAI.CubicEisenstein
open scoped MatrixGroups ContDiff
noncomputable section

theorem sourceArchHeight_upperSection (z : ℂ) (y : ℝ) (hy : 0 < y) :
    sourceArchHeight (upperSection z y hy : GL (Fin 2) ℂ) = y := by
  have h10 : (upperSection z y hy : GL (Fin 2) ℂ) 1 0 = 0 := rfl
  have h11 : (upperSection z y hy : GL (Fin 2) ℂ) 1 1 = (Real.sqrt y : ℂ)⁻¹ := rfl
  rw [sourceArchHeight, SpecialLinearGroup.coeToGL_det, Units.val_one, norm_one,
    sourceArchBottomNorm, h10, h11, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add,
    norm_inv, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg y), inv_pow,
    Real.sq_sqrt hy.le]
  simp

theorem sourceArchSphericalGL_upperSection (s z : ℂ) (y : ℝ) (hy : 0 < y) :
    sourceArchSphericalGL s (upperSection z y hy : GL (Fin 2) ℂ) = (y : ℂ) ^ (2 * s + 1) := by
  rw [sourceArchSphericalGL, sourceArchHeight_upperSection]

def sourceArchCoordinateProfile (s : ℂ) (p : EuclideanSpatial) : ℂ :=
  positiveHeightPower (2 * s + 1) (p 2)

theorem sourceArchCoordinateProfile_eq_section (s : ℂ) (p : EuclideanSpatial)
    (hp : 0 < p 2) :
    sourceArchSphericalSection s (ProjGenLinGroup.mk
      (upperSection ((p 0 : ℂ) + (p 1 : ℂ) * Complex.I) (p 2) hp : GL (Fin 2) ℂ)) =
      sourceArchCoordinateProfile s p := by
  rw [sourceArchSphericalSection_mk, sourceArchSphericalGL_upperSection,
    sourceArchCoordinateProfile, positiveHeightPower_eq_cpow _ _ hp]

theorem sourceArchCoordinateProfile_contDiffAt (s : ℂ) (p : EuclideanSpatial)
    (hp : 0 < p 2) : ContDiffAt ℝ ∞ (sourceArchCoordinateProfile s) p := by
  exact (positiveHeightPower_contDiffAt (2 * s + 1) (p 2) hp.ne').comp p
    (by fun_prop)

theorem sourceArchCoordinateProfile_laplacian (s c : ℂ) (p : EuclideanSpatial)
    (hp : 0 < p 2) :
    positiveEuclideanLaplacian (fun q => c * sourceArchCoordinateProfile s q) p =
      (1 - 4 * s ^ 2) * (c * sourceArchCoordinateProfile s p) := by
  have hsmooth : ∀ q : EuclideanSpatial, 0 < q 2 →
      ContDiffAt ℝ ∞ (fun q => c * sourceArchCoordinateProfile s q) q := by
    intro q hq
    exact contDiffAt_const.mul (sourceArchCoordinateProfile_contDiffAt s q hq)
  rw [positiveEuclideanLaplacian_eq_axis _ hsmooth p hp]
  change -axisLaplacian (fun q : SpatialCoordinates =>
    c * positiveHeightPower (2 * s + 1) (q 2)) p.ofLp = _
  rw [axisLaplacian_const_mul,
    axisLaplacian_eq_hyperbolicLaplacian
      (fun _ _ y => positiveHeightPower (2 * s + 1) y) p.ofLp]
  simp only [hyperbolicLaplacian, deriv_const']
  rw [(positiveHeightPower_hasDerivAt (2 * s + 1) (p 2) hp.ne').deriv,
    (positiveHeightPower_hasDerivAt_deriv (2 * s + 1) (p 2) hp.ne').deriv]
  unfold sourceArchCoordinateProfile
  field_simp [Complex.ofReal_ne_zero.mpr hp.ne']
  ring

theorem sourceArchCoordinateProfile_eigen (s : ℂ) (p : EuclideanSpatial) (hp : 0 < p 2) :
    positiveEuclideanLaplacian (sourceArchCoordinateProfile s) p =
      (1 - 4 * s ^ 2) * sourceArchCoordinateProfile s p := by
  simpa only [one_mul] using sourceArchCoordinateProfile_laplacian s 1 p hp

end
end ArtinMatthews.SourceArchJacquet
