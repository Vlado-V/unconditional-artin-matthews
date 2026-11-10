module

public import ArtinMatthews.MarkedMinorArcShearOperator
public import ArtinMatthews.MarkedMajorArcCircleSource
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
public import Mathlib.Order.Interval.Finset.Box
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

/-! The natural endpoint polynomial uses the same normalized circle and
positive phase as the finite product-shift pairing. -/
namespace ArtinMatthews
open MeasureTheory AddCircle
open scoped BigOperators
noncomputable section
local instance : Fact (0 < (1:ℝ)) := ⟨by norm_num⟩
local notation "Circle1" => AddCircle (1:ℝ)
local notation "e" => OAI.Problem337.RealPhase.phase

def giantComparisonNatFourier (S : Finset ℕ) (a : ℕ → ℂ) : C(Circle1, ℂ) :=
  markedProductFourierPolynomial (S.map Nat.castEmbedding) (fun n => a n.val.toNat)

theorem giantComparisonNatFourier_apply (S : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) :
    giantComparisonNatFourier S a (t:Circle1) = ∑ n ∈ S, a n*e (t*(n:ℝ)) := by
  unfold giantComparisonNatFourier
  simp only [markedProductFourierPolynomial,ContinuousMap.sum_apply,ContinuousMap.smul_apply,
    smul_eq_mul,markedMajor_fourier_phase]
  rw [Finset.sum_coe_sort (S.map Nat.castEmbedding) (fun n : ℤ => a n.toNat*e (t*(n:ℝ))),
    Finset.sum_map]
  simp

theorem giantComparisonNatFourier_parseval (S : Finset ℕ) (a : ℕ → ℂ) :
    (∫ θ : Circle1, ‖giantComparisonNatFourier S a θ‖^2 ∂AddCircle.haarAddCircle) =
      ∑ n ∈ S, ‖a n‖^2 := by
  unfold giantComparisonNatFourier
  rw [markedProductFourierPolynomial_parseval,
    Finset.sum_coe_sort (S.map Nat.castEmbedding) (fun n : ℤ => ‖a n.toNat‖^2), Finset.sum_map]
  simp

end
end ArtinMatthews
