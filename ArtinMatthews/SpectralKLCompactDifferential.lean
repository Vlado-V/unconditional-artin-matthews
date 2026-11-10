module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Mathlib.Order.CompletePartialOrder
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set MeasureTheory Filter
open scoped Topology ContDiff
noncomputable section

theorem spectralPositiveCompactProduct_continuous (u v : ℝ → ℂ)
    (hu : ∀ x : ℝ, 0 < x → ContinuousAt u x) (hv : Continuous v)
    (hp : tsupport v ⊆ Ioi (0 : ℝ)) : Continuous (fun x => u x * v x) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x ∈ tsupport v
  · exact (hu x (hp hx)).mul hv.continuousAt
  · have hz := notMem_tsupport_iff_eventuallyEq.mp hx
    have heq : (fun y => u y * v y) =ᶠ[𝓝 x] (fun _ => (0 : ℂ)) := by
      filter_upwards [hz] with y hy
      simp only [hy, Pi.zero_apply, mul_zero]
    exact continuousAt_const.congr heq.symm

theorem spectralPositiveCompactProduct_integrable (u v : ℝ → ℂ)
    (hu : ∀ x : ℝ, 0 < x → ContinuousAt u x) (hv : Continuous v)
    (hc : HasCompactSupport v) (hp : tsupport v ⊆ Ioi (0 : ℝ)) :
    Integrable (fun x => u x * v x) :=
  (spectralPositiveCompactProduct_continuous u v hu hv hp).integrable_of_hasCompactSupport hc.mul_left

def spectralKLCompactFlux (g : ℝ → ℂ) (x : ℝ) : ℂ := (x : ℂ) * deriv g x

def spectralKLPhysicalOperator (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  -(x : ℂ) * deriv (spectralKLCompactFlux g) x + (x : ℂ) ^ 2 * g x

theorem spectralKLCompactFlux_tsupport (g : ℝ → ℂ) :
    tsupport (spectralKLCompactFlux g) ⊆ tsupport g :=
  (tsupport_mul_subset_right (f := fun x : ℝ => (x : ℂ)) (g := deriv g)).trans tsupport_deriv_subset

theorem spectralKLCompactFlux_smooth (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (spectralKLCompactFlux g) :=
  Complex.ofRealCLM.contDiff.mul (contDiff_infty_iff_deriv.mp hg).2

theorem spectralKLPhysicalOperator_smooth (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (spectralKLPhysicalOperator g) := by
  have hf := spectralKLCompactFlux_smooth g hg
  exact (Complex.ofRealCLM.contDiff.neg.mul (contDiff_infty_iff_deriv.mp hf).2).add
    ((Complex.ofRealCLM.contDiff.pow 2).mul hg)

theorem spectralKLPhysicalOperator_tsupport (g : ℝ → ℂ) :
    tsupport (spectralKLPhysicalOperator g) ⊆ tsupport g := by
  apply closure_minimal _ (isClosed_tsupport g)
  intro x hx
  by_contra hn
  have hg0 := image_eq_zero_of_notMem_tsupport hn
  have hflux : x ∉ tsupport (spectralKLCompactFlux g) :=
    fun hx => hn (spectralKLCompactFlux_tsupport g hx)
  have hd0 := deriv_of_notMem_tsupport hflux
  exact hx (by simp [spectralKLPhysicalOperator, hd0, hg0])

theorem spectralKLPhysicalOperator_compact (g : ℝ → ℂ) (hc : HasCompactSupport g) :
    HasCompactSupport (spectralKLPhysicalOperator g) :=
  hc.of_isClosed_subset (isClosed_tsupport _) (spectralKLPhysicalOperator_tsupport g)

end
end ArtinMatthews
