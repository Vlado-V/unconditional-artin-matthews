module

public import ArtinMatthews.SpectralGamma0CuspVerticalDerivative
public import ArtinMatthews.SpectralGamma0CuspMassSpace
public import ArtinMatthews.SpectralGamma0CuspMassQuadratic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! Actual normalized constant-term operators in weighted vertical L².  The
horizontal mass factor remains in the target measure. -/

noncomputable section
open Set MeasureTheory
open scoped ENNReal MatrixGroups

namespace ArtinMatthews

def cuspHyperbolicConstantTerm (w Y : ℝ) (hY : 0 < Y) :
    CuspHyperbolicL2 w Y →L[ℂ] CuspVerticalL2 w Y :=
  (cuspVerticalPullback w Y).toContinuousLinearMap.adjoint.comp
    (cuspHyperbolicPullback w Y hY).toContinuousLinearMap.adjoint

theorem cuspHyperbolicConstantTerm_norm (w Y : ℝ) (hY : 0 < Y) :
    ‖cuspHyperbolicConstantTerm w Y hY‖ ≤ 1 := by
  have hU := (cuspHyperbolicPullback w Y hY).norm_toContinuousLinearMap_le
  have hV := (cuspVerticalPullback w Y).norm_toContinuousLinearMap_le
  have hUa : ‖(cuspHyperbolicPullback w Y hY).toContinuousLinearMap.adjoint‖ ≤ 1 := by
    simpa only [ContinuousLinearMap.adjoint.norm_map] using hU
  have hVa : ‖(cuspVerticalPullback w Y).toContinuousLinearMap.adjoint‖ ≤ 1 := by
    simpa only [ContinuousLinearMap.adjoint.norm_map] using hV
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul hVa hUa (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))

theorem cuspHyperbolicConstantTerm_norm_apply (w Y : ℝ) (hY : 0 < Y)
    (f : CuspHyperbolicL2 w Y) : ‖cuspHyperbolicConstantTerm w Y hY f‖ ≤ ‖f‖ :=
  ((cuspHyperbolicConstantTerm w Y hY).le_opNorm f).trans
    (mul_le_of_le_one_left (norm_nonneg _) (cuspHyperbolicConstantTerm_norm w Y hY))

theorem cuspHyperbolicAverageProjection_factor_constantTerm (w Y : ℝ) (hY : 0 < Y)
    (f : CuspHyperbolicL2 w Y) :
    cuspHyperbolicAverageProjection w Y hY f =
      cuspHyperbolicPullback w Y hY
        (cuspVerticalPullback w Y (cuspHyperbolicConstantTerm w Y hY f)) := rfl

theorem cuspHyperbolicConstantTerm_eq_zero_iff (w Y : ℝ) (hY : 0 < Y)
    (f : CuspHyperbolicL2 w Y) :
    cuspHyperbolicConstantTerm w Y hY f = 0 ↔ cuspHyperbolicAverageProjection w Y hY f = 0 := by
  rw [cuspHyperbolicAverageProjection_factor_constantTerm]
  constructor
  · intro h
    rw [h]
    simp only [map_zero]
  · intro h
    have hU : cuspVerticalPullback w Y (cuspHyperbolicConstantTerm w Y hY f) = 0 := by
      apply (cuspHyperbolicPullback w Y hY).injective
      simpa only [map_zero] using h
    apply (cuspVerticalPullback w Y).injective
    simpa only [map_zero] using hU

def gamma0CuspConstantTerm (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) :
    Gamma0RegionL2 N →L[ℂ] CuspVerticalL2 (N : ℝ) Y :=
  (cuspHyperbolicConstantTerm (N : ℝ) Y hY).comp (gamma0CuspMassRestriction N r Y hY)

def gamma0CuspVerticalConstantTerm (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) :
    gamma0EnergySpace N →L[ℂ] CuspVerticalL2 (N : ℝ) Y :=
  (cuspHyperbolicConstantTerm (N : ℝ) Y hY).comp (gamma0CuspVerticalRestriction N r Y hY)

theorem gamma0CuspConstantTerm_norm_sq_quadratic (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (hY1 : Y ≤ 1) (f : Gamma0RegionL2 N) :
    ‖gamma0CuspConstantTerm N r Y hY f‖ ^ 2 ≤
      (25 * ((N : ℝ) + 1) / Y ^ 2) * ‖f‖ ^ 2 := by
  have hb := cuspHyperbolicConstantTerm_norm_apply (N : ℝ) Y hY
    (gamma0CuspMassRestriction N r Y hY f)
  exact ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hb).trans
    (gamma0CuspMassRestriction_norm_sq_quadratic N r Y hY hY1 f)

theorem mem_gamma0AllHeightCuspidalMassSpace_iff_constantTerm (N : ℕ) [NeZero N]
    (f : Gamma0RegionL2 N) :
    f ∈ gamma0AllHeightCuspidalMassSpace N ↔
      ∀ (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y), gamma0CuspConstantTerm N r Y hY f = 0 := by
  rw [mem_gamma0AllHeightCuspidalMassSpace_iff]
  simp only [gamma0CuspConstantTerm, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ← cuspHyperbolicConstantTerm_eq_zero_iff]

end ArtinMatthews
