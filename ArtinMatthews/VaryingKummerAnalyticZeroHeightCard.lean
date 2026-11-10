module

public import ArtinMatthews.VaryingKummerAnalyticZeroHeightWindow
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


set_option backward.privateInPublic true
@[expose] public section

/-! The actual multiplicity count bounds the number of distinct bad heights. -/
namespace OAI.PrimeDegreePackets.AnalyticGrowth
open ArtinMatthews.ReusedGrowth Complex
open scoped BigOperators
noncomputable section

lemma zeroHeightWindow_card_le {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (hfe : ∀ z, f (1-z) = f z)
    (hstrip : ∀ ρ, f ρ = 0 → ρ.re ≤ 1) (T : ℝ) :
    ((zeroHeightWindow f T).card : ℝ) ≤ zeroHeightCount f T := by
  unfold zeroHeightCount
  calc
    _ = ∑ ρ ∈ zeroHeightWindow f T, (1 : ℝ) := by simp
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro ρ hρ
      have hz := ((mem_zeroHeightWindow_iff hf h0 hfe hstrip T ρ).mp hρ).1
      have hm := (zeroMultiplicity_ne_zero_iff hf h0 ρ).mpr hz
      have hp : (1 : ℤ) ≤ zeroMultiplicity f ρ := by
        have hn := zeroMultiplicity_nonneg hf ρ
        omega
      exact_mod_cast hp

lemma zeroHeightImaginary_card_le {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (hfe : ∀ z, f (1-z) = f z)
    (hstrip : ∀ ρ, f ρ = 0 → ρ.re ≤ 1) (T : ℝ) :
    (((zeroHeightWindow f T).image Complex.im).card : ℝ) ≤ zeroHeightCount f T := by
  have hc : (((zeroHeightWindow f T).image Complex.im).card : ℝ) ≤
      ((zeroHeightWindow f T).card : ℝ) := by exact_mod_cast Finset.card_image_le
  exact hc.trans (zeroHeightWindow_card_le hf h0 hfe hstrip T)

end
end OAI.PrimeDegreePackets.AnalyticGrowth
