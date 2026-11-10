module

public import ArtinMatthews.MarkedOrderedLimits
public import ArtinMatthews.GiantFixedResidueActualRough
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! The actual positive sieve uses m rather than the paper's even depth.
At m=4n its exponential error agrees exactly, and its reciprocal
cutoff loss fits the established ordered-limit estimate. -/
namespace ArtinMatthews
open MeasureTheory
open scoped BigOperators
noncomputable section

theorem giantFixedProgression_sieve_exponents_compare (c : ℝ) (hc : 0 < c) (hc1 : c≤1)
    (n : ℕ) :
    1/markedSieveExponent c (4*n) ≤
      12/(markedCorrelationSieveExponent c (2*(n:ℝ)))^2 := by
  let A := 24*(4*(n:ℝ)+1)
  let B := 4*(2*(n:ℝ))+3
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hs : markedSieveExponent c (4*n) = c/A := by
    unfold markedSieveExponent A
    push_cast
    rfl
  have ht : markedCorrelationSieveExponent c (2*(n:ℝ)) = c/B := rfl
  have hn : A*c≤12*B^2 := by
    calc
      _ ≤ A*1 := mul_le_mul_of_nonneg_left hc1 hA.le
      _ ≤ _ := by dsimp [A,B]; nlinarith [sq_nonneg (n:ℝ),Nat.cast_nonneg (α:=ℝ) n]
  rw [hs,ht]
  calc
    1/(c/A) = (A*c)/c^2 := by field_simp
    _ ≤ (12*B^2)/c^2 := div_le_div_of_nonneg_right hn (sq_nonneg c)
    _ = _ := by field_simp

def giantFixedProgressionDepthConstant {M : ℕ} (U : Finset (ZMod M)ˣ)
    (Φ : ℝ → ℝ) (T : ℝ) : ℝ :=
  12*((U.card:ℝ)*2*(∫ t in Set.Ioc 0 T,Φ t)*Real.exp (-Real.eulerMascheroniConstant)/(M.totient:ℝ))

theorem giantFixedProgression_depth_error_le {M : ℕ} (U : Finset (ZMod M)ˣ)
    (Φ : ℝ → ℝ) (T c : ℝ) (hΦ : ∀ t,0≤Φ t) (hc : 0 < c) (hc1 : c≤1) (n : ℕ) :
    (U.card:ℝ)*giantFixedResidueRoughError M Φ T c (4*n) ≤
      giantFixedProgressionDepthConstant U Φ T*Real.exp (-(2*(n:ℝ)))/
        (markedCorrelationSieveExponent c (2*(n:ℝ)))^2 := by
  let F := (U.card:ℝ)*2*(∫ t in Set.Ioc 0 T,Φ t)*Real.exp (-Real.eulerMascheroniConstant)/(M.totient:ℝ)
  have hF : 0 ≤ F := by
    unfold F
    exact div_nonneg (mul_nonneg (mul_nonneg (by positivity) (integral_nonneg hΦ))
      (Real.exp_nonneg _)) (Nat.cast_nonneg _)
  have hExp : Real.exp (-((4*n:ℕ):ℝ)/2)=Real.exp (-(2*(n:ℝ))) := by
    congr 1
    push_cast
    ring
  calc
    _ = (F*Real.exp (-(2*(n:ℝ))))*(1/markedSieveExponent c (4*n)) := by
      unfold giantFixedResidueRoughError giantRoughSieveError F
      rw [hExp]
      ring
    _ ≤ (F*Real.exp (-(2*(n:ℝ))))*(12/(markedCorrelationSieveExponent c (2*(n:ℝ)))^2) :=
      mul_le_mul_of_nonneg_left (giantFixedProgression_sieve_exponents_compare c hc hc1 n)
        (mul_nonneg hF (Real.exp_nonneg _))
    _ = _ := by unfold giantFixedProgressionDepthConstant F; ring

end
end ArtinMatthews
