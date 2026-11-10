module

public import ArtinMatthews.SourceKPArchTranslatedProfile
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import OAI.NumberTheory.DirichletL.RowCompletion.CubicReopening


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceArchJacquet
open Matrix Matrix.GeneralLinearGroup OAI.CubicEisenstein
open scoped MatrixGroups Topology ContDiff
noncomputable section

theorem sourceArchTranslatedProfile_eq_exp (s : ℂ) (g : GL (Fin 2) ℂ)
    (p : SpatialCoordinates) :
    sourceArchTranslatedProfile s g (WithLp.toLp 2 p) =
      (‖(GeneralLinearGroup.det g : ℂ)‖ : ℂ) ^ (2*s+1) *
        Complex.exp ((2*s+1) * (rowLogHeight (sourceArchTranslatedRow g) p : ℂ)) := by
  rfl

theorem sourceArchTranslatedProfile_axis_derivative (s : ℂ) (g : GL (Fin 2) ℂ)
    (p : SpatialCoordinates) (hp : 0 < p 2) (j : Fin 3) :
    HasDerivAt (axisSlice (fun q => sourceArchTranslatedProfile s g (WithLp.toLp 2 q)) p j)
      (sourceArchTranslatedProfile s g (WithLp.toLp 2 p) * (2*s+1) *
        (rowLogD (sourceArchTranslatedRow g) p j : ℂ)) (p j) := by
  have hlog := rowLogHeight_hasDerivAt (sourceArchTranslatedRow g)
    (sourceArchTranslatedRow_ne_zero g) p hp j
  have he := (hlog.ofReal_comp.const_mul (2*s+1)).cexp.const_mul
    ((‖(GeneralLinearGroup.det g : ℂ)‖ : ℂ)^(2*s+1))
  convert he using 1
  · funext t
    exact sourceArchTranslatedProfile_eq_exp s g (Function.update p j t)
  · rw [sourceArchTranslatedProfile_eq_exp]
    simp only [Function.update_eq_self]
    ring

theorem sourceArchTranslatedProfile_axis_scaled_bound (s : ℂ) (g : GL (Fin 2) ℂ)
    (p : SpatialCoordinates) (hp : 0 < p 2) (j : Fin 3) :
    ‖(p 2 : ℂ) * deriv
      (axisSlice (fun q => sourceArchTranslatedProfile s g (WithLp.toLp 2 q)) p j) (p j)‖ ≤
      ‖2*s+1‖ * ‖sourceArchTranslatedProfile s g (WithLp.toLp 2 p)‖ := by
  rw [(sourceArchTranslatedProfile_axis_derivative s g p hp j).deriv]
  have he : (p 2 : ℂ) *
      (sourceArchTranslatedProfile s g (WithLp.toLp 2 p) * (2*s+1) *
        (rowLogD (sourceArchTranslatedRow g) p j : ℂ)) =
      ((p 2 * rowLogD (sourceArchTranslatedRow g) p j : ℝ) : ℂ) *
        ((2*s+1) * sourceArchTranslatedProfile s g (WithLp.toLp 2 p)) := by
    push_cast
    ring
  rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs,norm_mul]
  simpa using mul_le_mul_of_nonneg_right
    (rowLogD_hyperbolic_bound (sourceArchTranslatedRow g) (sourceArchTranslatedRow_ne_zero g) p hp j)
    (mul_nonneg (norm_nonneg (2*s+1)) (norm_nonneg (sourceArchTranslatedProfile s g (WithLp.toLp 2 p))))

theorem sourceArchTranslatedProfile_scaled_coordinate_bound (s : ℂ) (g : GL (Fin 2) ℂ)
    (p : EuclideanSpatial) (hp : 0 < p 2) (j : Fin 3) :
    ‖(p 2 : ℂ) * fderiv ℝ (sourceArchTranslatedProfile s g) p (euclideanCoordinateVector j)‖ ≤
      ‖2*s+1‖ * ‖sourceArchTranslatedProfile s g p‖ := by
  rw [← (euclideanAxisSlice_derivatives (sourceArchTranslatedProfile s g)
    (sourceArchTranslatedProfile_contDiffAt s g) p hp j).1]
  simpa using sourceArchTranslatedProfile_axis_scaled_bound s g p.ofLp hp j

theorem sourceArchTranslatedProfile_coordinate_bound (s : ℂ) (g : GL (Fin 2) ℂ)
    (p : EuclideanSpatial) (hp : 0 < p 2) (j : Fin 3) :
    ‖fderiv ℝ (sourceArchTranslatedProfile s g) p (euclideanCoordinateVector j)‖ ≤
      (‖2*s+1‖ / p 2) * ‖sourceArchTranslatedProfile s g p‖ := by
  have h := sourceArchTranslatedProfile_scaled_coordinate_bound s g p hp j
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hp] at h
  calc
    _ ≤ (‖2*s+1‖ * ‖sourceArchTranslatedProfile s g p‖) / p 2 := by
      apply (le_div_iff₀ hp).mpr
      nlinarith
    _ = _ := by ring

theorem euclideanThreeLinear_opNorm_bound (L : EuclideanSpatial →L[ℝ] ℂ)
    (B : ℝ) (hB : 0 ≤ B) (hL : ∀ j, ‖L (euclideanCoordinateVector j)‖ ≤ B) :
    ‖L‖ ≤ 3*B := by
  apply L.opNorm_le_bound (by positivity)
  intro v
  have hv : v = v 0 • euclideanCoordinateVector 0 + v 1 • euclideanCoordinateVector 1 +
      v 2 • euclideanCoordinateVector 2 := by
    apply (WithLp.equiv 2 (Fin 3 → ℝ)).injective
    funext j
    fin_cases j <;> simp [euclideanCoordinateVector]
  have hLv : L v = v 0 • L (euclideanCoordinateVector 0) +
      v 1 • L (euclideanCoordinateVector 1) + v 2 • L (euclideanCoordinateVector 2) := by
    conv_lhs => rw [hv]
    simp only [L.map_add,L.map_smul]
  rw [hLv]
  calc
    _ ≤ ‖v 0 • L (euclideanCoordinateVector 0)‖ + ‖v 1 • L (euclideanCoordinateVector 1)‖ +
        ‖v 2 • L (euclideanCoordinateVector 2)‖ := (norm_add_le _ _).trans
      (add_le_add (norm_add_le _ _) le_rfl)
    _ = ‖v 0‖*‖L (euclideanCoordinateVector 0)‖ + ‖v 1‖*‖L (euclideanCoordinateVector 1)‖ +
        ‖v 2‖*‖L (euclideanCoordinateVector 2)‖ := by simp only [norm_smul]
    _ ≤ ‖v‖*B + ‖v‖*B + ‖v‖*B := by
      gcongr <;> first | exact hL _ | exact PiLp.norm_apply_le _ _
    _ = (3*B)*‖v‖ := by ring

theorem sourceArchTranslatedProfile_fderiv_bound (s : ℂ) (g : GL (Fin 2) ℂ)
    (p : EuclideanSpatial) (hp : 0 < p 2) :
    ‖fderiv ℝ (sourceArchTranslatedProfile s g) p‖ ≤
      (3 * ‖2*s+1‖ / p 2) * ‖sourceArchTranslatedProfile s g p‖ := by
  have h := euclideanThreeLinear_opNorm_bound (fderiv ℝ (sourceArchTranslatedProfile s g) p)
    ((‖2*s+1‖ / p 2)*‖sourceArchTranslatedProfile s g p‖) (by positivity)
    (sourceArchTranslatedProfile_coordinate_bound s g p hp)
  calc
    _ ≤ 3 * ((‖2*s+1‖ / p 2)*‖sourceArchTranslatedProfile s g p‖) := h
    _ = _ := by ring

end
end ArtinMatthews.SourceArchJacquet
