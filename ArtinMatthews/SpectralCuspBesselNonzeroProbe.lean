module

public import ArtinMatthews.SpectralCuspBesselTransform
public import ArtinMatthews.SpectralBesselODEUniqueness
public import ArtinMatthews.SpectralCuspConstantTermWeakDerivative
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
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
public import Mathlib.Order.CompletePartialOrder
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

/-! A nonzero compact height probe exists for the genuine K kernel above
any positive height. This uses its actual ODE nonvanishing and weak-test
density, with no nonzero transform assumption. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff

namespace ArtinMatthews

theorem cuspBesselTransform_exists_nonzero_probe (ν : ℂ) (hν : -1/2 < ν.re)
    (q Y : ℝ) (hq : 0 < q) (hY : 0 < Y) :
    ∃ ρ : ℝ → ℝ, ContDiff ℝ ∞ ρ ∧ HasCompactSupport ρ ∧
      tsupport ρ ⊆ Ioi Y ∧ cuspBesselTransform ν q Y ρ ≠ 0 := by
  by_contra hn
  push Not at hn
  let f := cuspBesselKernel ν q
  have hfc : ContinuousOn f (Ioi Y) := fun y hy =>
    (cuspBesselKernel_continuousAt ν hq (hY.trans hy)).continuousWithinAt
  have hfl : LocallyIntegrableOn f (Ioi Y) := hfc.locallyIntegrableOn measurableSet_Ioi
  have htest (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
      (hsρ : tsupport ρ ⊆ Ioi Y) : (∫ y,ρ y • f y) = 0 := by
    let σ (y : ℝ) := ρ y*y^2
    have hσ : ContDiff ℝ ∞ σ := hρ.mul (contDiff_id.pow 2)
    have hcσ : HasCompactSupport σ := hcρ.mul_right
    have hsσ : tsupport σ ⊆ Ioi Y := tsupport_mul_subset_left.trans hsρ
    have hz : cuspBesselTransform ν q Y σ = 0 := hn σ hσ hcσ hsσ
    rw [← spectralTest_setIntegral_eq_integral ρ (Ioi Y) hsρ]
    calc
      _ = cuspBesselTransform ν q Y σ := by
        unfold cuspBesselTransform
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
        have hy0 : 0 < y := hY.trans hy
        dsimp only [σ,cuspBesselTransformIntegrand]
        rw [mul_div_cancel_right₀ (ρ y) (pow_ne_zero 2 hy0.ne')]
        rfl
      _ = 0 := hz
  have hz := isOpen_Ioi.ae_eq_zero_of_integral_contDiff_smul_eq_zero hfl htest
  have haz : f =ᵐ[volume.restrict (Ioi Y)] (fun _ => 0) := by
    filter_upwards [ae_restrict_of_ae hz,ae_restrict_mem measurableSet_Ioi] with y hy hyY
    exact hy hyY
  have heq := Measure.eqOn_open_of_ae_eq (μ := volume) haz isOpen_Ioi hfc continuousOn_const
  obtain ⟨y,hy0,hyY,hne⟩ := spectralKBesselWhittaker_exists_ne_zero_above ν hν q Y hq
  apply hne
  rw [spectralKBesselWhittaker_eq_sqrt ν q y hy0.le]
  exact heq hyY

end ArtinMatthews
