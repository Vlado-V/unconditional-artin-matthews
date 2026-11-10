module

public import ArtinMatthews.SpectralABLOppositeModulus
public import ArtinMatthews.SpectralCuspEisensteinWidthFormula
public import ArtinMatthews.SpectralJOddSynthesis
public import ArtinMatthews.SpectralJRealTestParts
public import ArtinMatthews.SpectralJMixedGeometric
public import ArtinMatthews.SpectralJSourceTestSplit
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

namespace ArtinMatthews
open MeasureTheory Set Complex
open scoped ContDiff MatrixGroups
noncomputable section

theorem gamma0MixedJ_geometric_parts
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hp : tsupport f ⊆ Ioi (0 : ℝ))
    (r s : ℕ) [NeZero r] [NeZero s] (hcop : r.Coprime s)
    (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) (hmn : 0 < m * n) :
    (∑' q : Ioi (0 : ℕ),
      gamma0ABLOppositeGeometricTerm (r * s) (gamma0CuspOneOver s) 1 q n m f) =
      (∑' q : Ioi (0 : ℕ),
        gamma0ABLOppositeGeometricTerm (r * s) (gamma0CuspOneOver s) 1 q n m
          (spectralJRealTest f)) +
      I * (∑' q : Ioi (0 : ℕ),
        gamma0ABLOppositeGeometricTerm (r * s) (gamma0CuspOneOver s) 1 q n m
          (spectralJImagTest f)) ∧
    (∑' q : Ioi (0 : ℕ),
      gamma0ABLOppositeGeometricTerm (r * s) (gamma0CuspOneOver s) 1 q n m
        (spectralJOddSynthesis f)) =
      (∑' q : Ioi (0 : ℕ),
        gamma0ABLOppositeGeometricTerm (r * s) (gamma0CuspOneOver s) 1 q n m
          (spectralJOddSynthesis (spectralJRealTest f))) +
      I * (∑' q : Ioi (0 : ℕ),
        gamma0ABLOppositeGeometricTerm (r * s) (gamma0CuspOneOver s) 1 q n m
          (spectralJOddSynthesis (spectralJImagTest f))) := by
  have hR := gamma0MixedJ_geometric_reconstruction (spectralJRealTest f)
    (spectralJRealTest_contDiff f hf) (spectralJRealTest_hasCompactSupport f hc)
    ((spectralJRealTest_tsupport f).trans hp) r s hcop m n hm hn hmn
  have hI := gamma0MixedJ_geometric_reconstruction (spectralJImagTest f)
    (spectralJImagTest_contDiff f hf) (spectralJImagTest_hasCompactSupport f hc)
    ((spectralJImagTest_tsupport f).trans hp) r s hcop m n hm hn hmn
  constructor
  · have hpoint (q : Ioi (0 : ℕ)) :
        gamma0ABLOppositeGeometricTerm (r * s) (gamma0CuspOneOver s) 1 q n m f =
          gamma0ABLOppositeGeometricTerm (r * s) (gamma0CuspOneOver s) 1 q n m
            (spectralJRealTest f) +
          I * gamma0ABLOppositeGeometricTerm (r * s) (gamma0CuspOneOver s) 1 q n m
            (spectralJImagTest f) := by
      dsimp only [gamma0ABLOppositeGeometricTerm]
      have hparts := congrFun (spectralJTest_parts f)
        (4 * Real.pi * Real.sqrt (|(n : ℝ) * (m : ℝ)|) /
          gamma0TrueWidthModulus (r * s) (gamma0CuspOneOver s) 1 (q.val : ℝ))
      simp only [Pi.add_apply] at hparts
      rw [hparts]
      ring
    simp_rw [hpoint]
    rw [hR.1.of_norm.tsum_add (hI.1.of_norm.mul_left I), tsum_mul_left]
  · have hpoint (q : Ioi (0 : ℕ)) :
        gamma0ABLOppositeGeometricTerm (r * s) (gamma0CuspOneOver s) 1 q n m
          (spectralJOddSynthesis f) =
          gamma0ABLOppositeGeometricTerm (r * s) (gamma0CuspOneOver s) 1 q n m
            (spectralJOddSynthesis (spectralJRealTest f)) +
          I * gamma0ABLOppositeGeometricTerm (r * s) (gamma0CuspOneOver s) 1 q n m
            (spectralJOddSynthesis (spectralJImagTest f)) := by
      dsimp only [gamma0ABLOppositeGeometricTerm]
      rw [spectralJOddSynthesis_parts f hf.continuous hc hp]
      ring
    simp_rw [hpoint]
    rw [hR.2.1.of_norm.tsum_add (hI.2.1.of_norm.mul_left I), tsum_mul_left]

end
end ArtinMatthews
