module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.RepresentationTheory.Theta.RealFourier
public import Mathlib.Analysis.Fourier.AddCircleMulti
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
public import OAI.RepresentationTheory.Theta.PeriodizationIntegral


set_option backward.privateInPublic true
@[expose] public section

/-! # Real Poisson -/

namespace OAI.RepresentationTheory.Theta.RealPoisson.AutomorphyConstruction

noncomputable section

section

/-! Multivariable Poisson summation for coordinate Schwartz functions. -/

open scoped Classical
open _root_.MeasureTheory

variable {ι : Type*} [Fintype ι]

theorem mFourier_projection (n : ι → ℤ) (x : ι → ℝ) :
    UnitAddTorus.mFourier n (RealFourier.PoissonAutomorphyConstruction.torusProjection x) =
      PoissonAutomorphyNormalizationData.standardRealCharacter (∑ i, (n i : ℝ) * x i) := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, RealFourier.PoissonAutomorphyConstruction.torusProjection,
    fourier_coe_apply, Complex.ofReal_one, div_one, PoissonAutomorphyNormalizationData.standardRealCharacter_apply]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem torusPeriodization_fourierCoeff_eq (f : SchwartzMap (ι → ℝ) ℂ) (n : ι → ℤ) :
    UnitAddTorus.mFourierCoeff (RealFourier.PoissonAutomorphyConstruction.torusPeriodization f) n =
      PoissonAutomorphyNormalizationData.fourier PoissonAutomorphyNormalizationData.standardRealCharacter volume f (RealFourier.PoissonAutomorphyConstruction.integerReal n) := by
  rw [PeriodizationIntegral.PoissonAutomorphyConstruction.torusPeriodization_fourierCoeff, PoissonAutomorphyNormalizationData.fourier]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    dsimp only
    rw [mFourier_projection]
    simp only [Pi.neg_apply, Int.cast_neg, neg_mul, Finset.sum_neg_distrib, RealFourier.PoissonAutomorphyConstruction.integerReal]
    exact mul_comm _ _

theorem real_poisson_summation_shift (f : SchwartzMap (ι → ℝ) ℂ) (x : ι → ℝ) :
    (∑' n : ι → ℤ, f (x + RealFourier.PoissonAutomorphyConstruction.integerReal n)) =
      ∑' n : ι → ℤ, PoissonAutomorphyNormalizationData.fourier PoissonAutomorphyNormalizationData.standardRealCharacter volume f (RealFourier.PoissonAutomorphyConstruction.integerReal n) *
        PoissonAutomorphyNormalizationData.standardRealCharacter (∑ i, (n i : ℝ) * x i) := by
  have hsum : Summable (UnitAddTorus.mFourierCoeff (RealFourier.PoissonAutomorphyConstruction.torusPeriodization f)) := by
    exact (RealFourier.PoissonAutomorphyConstruction.coordinateFourier_integer_summable f).of_norm.congr
      (fun n => (torusPeriodization_fourierCoeff_eq f n).symm)
  have h := UnitAddTorus.hasSum_mFourier_series_apply_of_summable hsum (RealFourier.PoissonAutomorphyConstruction.torusProjection x)
  simpa only [RealFourier.PoissonAutomorphyConstruction.torusPeriodization_projection, torusPeriodization_fourierCoeff_eq,
    smul_eq_mul, mFourier_projection] using h.tsum_eq.symm

theorem real_poisson_summation (f : SchwartzMap (ι → ℝ) ℂ) :
    (∑' n : ι → ℤ, f (RealFourier.PoissonAutomorphyConstruction.integerReal n)) =
      ∑' n : ι → ℤ, PoissonAutomorphyNormalizationData.fourier PoissonAutomorphyNormalizationData.standardRealCharacter volume f (RealFourier.PoissonAutomorphyConstruction.integerReal n) := by
  simpa only [zero_add, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
    AddChar.map_zero_eq_one, mul_one] using real_poisson_summation_shift f 0

end

/-! Poisson summation after a positive real dilation. -/

open scoped Classical
open _root_.MeasureTheory

variable {ι : Type*} [Fintype ι]

def realScaleEquiv (r : ℝ) (hr : r ≠ 0) : (ι → ℝ) ≃L[ℝ] (ι → ℝ) where
  toLinearEquiv := LinearEquiv.smulOfUnit (Units.mk0 r hr)
  continuous_toFun := continuous_const_smul (Units.mk0 r hr)
  continuous_invFun := continuous_const_smul (Units.mk0 r hr)⁻¹

def scaledRealSchwartz (r : ℝ) (hr : r ≠ 0) (f : SchwartzMap (ι → ℝ) ℂ) :
    SchwartzMap (ι → ℝ) ℂ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (realScaleEquiv r hr) f

theorem scaledRealSchwartz_apply (r : ℝ) (hr : r ≠ 0) (f : SchwartzMap (ι → ℝ) ℂ) (x : ι → ℝ) :
    scaledRealSchwartz r hr f x = f (r • x) := rfl

theorem fourier_scaledRealSchwartz (r : ℝ) (hr : 0 < r) (f : SchwartzMap (ι → ℝ) ℂ) (x : ι → ℝ) :
    PoissonAutomorphyNormalizationData.fourier PoissonAutomorphyNormalizationData.standardRealCharacter volume (scaledRealSchwartz r hr.ne' f) x =
      (((r ^ Fintype.card ι)⁻¹ : ℝ) : ℂ) *
        PoissonAutomorphyNormalizationData.fourier PoissonAutomorphyNormalizationData.standardRealCharacter volume f (r⁻¹ • x) := by
  let F : (ι → ℝ) → ℂ := fun y => f y * PoissonAutomorphyNormalizationData.standardRealCharacter (-(∑ i, (r⁻¹ • x) i * y i))
  have hpair (y : ι → ℝ) : (∑ i, (r⁻¹ • x) i * (r • y) i) = ∑ i, x i * y i := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.smul_apply, smul_eq_mul]
    calc
      _ = (r⁻¹ * r) * (x i * y i) := by ring
      _ = _ := by rw [inv_mul_cancel₀ hr.ne', one_mul]
  have heq : (fun y => scaledRealSchwartz r hr.ne' f y * PoissonAutomorphyNormalizationData.standardRealCharacter (-(∑ i, x i * y i))) =
      fun y => F (r • y) := by
    funext y
    simp only [F, hpair, scaledRealSchwartz_apply]
  rw [PoissonAutomorphyNormalizationData.fourier, heq, Measure.integral_comp_smul_of_nonneg volume F r (hR := hr.le)]
  simp only [Module.finrank_fintype_fun_eq_card, Complex.real_smul]
  rfl

theorem real_poisson_summation_scaled (r : ℝ) (hr : 0 < r)
    (f : SchwartzMap (ι → ℝ) ℂ) (a : ι → ℝ) :
    (∑' m : ι → ℤ, f (a + r • RealFourier.PoissonAutomorphyConstruction.integerReal m)) =
      (((r ^ Fintype.card ι)⁻¹ : ℝ) : ℂ) *
        ∑' k : ι → ℤ, PoissonAutomorphyNormalizationData.fourier PoissonAutomorphyNormalizationData.standardRealCharacter volume f (r⁻¹ • RealFourier.PoissonAutomorphyConstruction.integerReal k) *
          PoissonAutomorphyNormalizationData.standardRealCharacter (∑ i, (k i : ℝ) * (r⁻¹ * a i)) := by
  have h := real_poisson_summation_shift (scaledRealSchwartz r hr.ne' f) (r⁻¹ • a)
  simp only [scaledRealSchwartz_apply, smul_add, smul_smul, mul_inv_cancel₀ hr.ne',
    one_smul, fourier_scaledRealSchwartz r hr, Pi.smul_apply, smul_eq_mul] at h
  rw [← tsum_mul_left]
  exact h.trans (tsum_congr fun k => mul_assoc _ _ _)

end

end OAI.RepresentationTheory.Theta.RealPoisson.AutomorphyConstruction
