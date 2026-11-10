module

public import ArtinMatthews.PositiveDensityCubicPrimeBaseline
public import ArtinMatthews.CubicThetaActualCuspFormConstructed
public import ArtinMatthews.PositiveDensityCubicCuspStatistic
public import ArtinMatthews.GiantProgressionSmoothMean
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! The proved shifted prime baseline converts the centered statistic of
the actual native cubic cusp form to its uncentered statistic. -/

noncomputable section
namespace ArtinMatthews

open Filter UpperHalfPlane
open OAI OAI.SevenEighths
open scoped MatrixGroups BigOperators Topology Asymptotics ContDiff

def giantCubicCuspCenteredPrimeTest {A : ℤ}
    (f : CuspForm (cubicThetaKernel (cubicNumeratorThetaLevel A)) 1)
    (twist : ℕ → ℂ) (ε : ℝ) (Φ : ℝ → ℝ) (T x : ℝ) : ℂ :=
  ∑ p ∈ giantPrimeMeanRange T x,
    (giantSieveWeight Φ x p : ℂ) * twist p *
      ((((giantPrimeFactors (p - 1) x ε).card : ℝ) - giantPrimeReciprocalSum x ε : ℝ) : ℂ) *
      (qExpansion 1 f).coeff p

theorem giantCubicCuspPrimeTest_eq_centered_add_baseline (A : ℤ) (hA : A ≠ 0)
    (hnoncube : ¬ ∃ y : OAI.CubicFirstMoment.Eisenstein,
      y ^ 3 = (A : OAI.CubicFirstMoment.Eisenstein))
    {M : ℕ} (χ : DirichletCharacter ℂ M) (ε : ℝ) (Φ : ℝ → ℝ) (T x : ℝ) :
    let f := actualCubicNumeratorHeckeThetaCuspForm A hA hnoncube
    giantCubicCuspPrimeTest f (fun p => χ p) ε Φ T x =
      giantCubicCuspCenteredPrimeTest f (fun p => χ p) ε Φ T x +
        (giantPrimeReciprocalSum x ε : ℂ) *
          giantCubicShiftedPrimeBaseline (cubicNumeratorHeckeCharacter A hA) χ Φ T x := by
  simp only [giantCubicCuspPrimeTest, giantCubicCuspCenteredPrimeTest,
    giantCubicShiftedPrimeBaseline, giantSieveWeight,
    actualCubicNumeratorHeckeThetaCuspForm_qExpansion_coeff, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _hp
  push_cast
  ring

theorem giantCubicCuspPrimeTest_mean_of_centered (A : ℤ) (hA : A ≠ 0)
    (hnoncube : ¬ ∃ y : OAI.CubicFirstMoment.Eisenstein,
      y ^ 3 = (A : OAI.CubicFirstMoment.Eisenstein))
    {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M)
    {ε : ℝ} (hε : 0 < ε) (hε₁ : ε < 1)
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ) (hc : HasCompactSupport Φ)
    {T : ℝ} (hT : 1 < T) (hs : Function.support Φ ⊆ Set.Ioo 1 T)
    (hcentered : giantCubicCuspCenteredPrimeTest
      (actualCubicNumeratorHeckeThetaCuspForm A hA hnoncube) (fun p => χ p) ε Φ T
      =o[atTop] (fun x : ℝ => x / Real.log x)) :
    Tendsto (fun x : ℝ => ((Real.log x / x : ℝ) : ℂ) *
      giantCubicCuspPrimeTest (actualCubicNumeratorHeckeThetaCuspForm A hA hnoncube)
        (fun p => χ p) ε Φ T x) atTop (𝓝 0) := by
  have hbase := giant_normalized_complex_of_isLittleO _
    (giantCubicShiftedPrimeBaseline_isLittleO A hA hnoncube χ Φ hΦ hc hT hs)
  have hzero := giant_normalized_complex_of_isLittleO _ hcentered
  have hC := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (giantPrimeReciprocalSum_tendsto hε hε₁)
  have h := hzero.add (hC.mul hbase)
  simp only [Function.comp_def, mul_zero, add_zero] at h
  apply h.congr
  intro x
  rw [giantCubicCuspPrimeTest_eq_centered_add_baseline A hA hnoncube χ ε Φ T x]
  ring

end ArtinMatthews
