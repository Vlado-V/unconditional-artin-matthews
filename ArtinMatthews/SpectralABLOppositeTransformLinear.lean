module

public import ArtinMatthews.SpectralABLOppositeKTransform
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

namespace ArtinMatthews
open MeasureTheory Complex
open scoped BigOperators
noncomputable section

theorem spectralABLOppositeTransform_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℂ) (z : ℂ)
    (hI : ∀ i ∈ s, Integrable (spectralKLCompactOrderIntegrand (f i) (2*I*z))) :
    spectralABLOppositeTransform (fun x => ∑ i ∈ s, f i x) z =
      ∑ i ∈ s, spectralABLOppositeTransform (f i) z := by
  have he : spectralKLCompactOrderIntegrand (fun x => ∑ i ∈ s, f i x) (2*I*z) =
      fun x => ∑ i ∈ s, spectralKLCompactOrderIntegrand (f i) (2*I*z) x := by
    funext x
    simp only [spectralKLCompactOrderIntegrand,spectralKLPhysicalCompactDiv,div_eq_mul_inv,
      Finset.sum_mul,Finset.mul_sum]
  simp only [spectralABLOppositeTransform,spectralABLOppositeFourierWeight,spectralKLCompactOrderTransform,he]
  rw [integral_finsetSum s hI,Finset.mul_sum,Finset.mul_sum]

end
end ArtinMatthews
