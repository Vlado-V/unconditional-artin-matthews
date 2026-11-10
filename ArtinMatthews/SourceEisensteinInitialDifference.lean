module

public import ArtinMatthews.SourceEisensteinNonconstant
public import ArtinMatthews.SourceKPAdelicCuspCutoff
public import ArtinMatthews.SourceKPAdelicCutoffSupport
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

/-! The original Eisenstein-minus-cutoff function splits into its genuine nonconstant and outgoing terms. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain
open scoped NumberField AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPAdelicInitialDifference (T : ℝ) (s : ℂ) (q : SourceKPAdelicProjective K hζ) : ℂ :=
  sourceKPAdelicCompactEisenstein K hζ s q - sourceKPAdelicCutoffEisenstein K hζ T s q

theorem sourceKPAdelicInitialDifference_high {T : ℝ} (hT : 1 ≤ T) (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) (hq : 2 * T ≤ sourceKPAdelicCoverHeight K hζ q) :
    sourceKPAdelicInitialDifference K hζ T s q =
      sourceKPAdelicNonconstantEisenstein K hζ s q + sourceKPAdelicTraceIntertwiner K hζ s q := by
  rw [sourceKPAdelicInitialDifference, sourceKPAdelicCutoffEisenstein_eq_of_high K hζ hT s q hq,
    sourceKPAdelicNonconstantEisenstein]
  ring

theorem sourceKPAdelicInitialDifference_high_norm_sq {T : ℝ} (hT : 1 ≤ T) (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) (hq : 2 * T ≤ sourceKPAdelicCoverHeight K hζ q) :
    ‖sourceKPAdelicInitialDifference K hζ T s q‖ ^ 2 ≤
      2 * ‖sourceKPAdelicNonconstantEisenstein K hζ s q‖ ^ 2 +
        2 * ‖sourceKPAdelicTraceIntertwiner K hζ s q‖ ^ 2 := by
  rw [sourceKPAdelicInitialDifference_high K hζ hT s q hq]
  have hnorm := norm_add_le (sourceKPAdelicNonconstantEisenstein K hζ s q)
    (sourceKPAdelicTraceIntertwiner K hζ s q)
  have hsq := sq_nonneg (‖sourceKPAdelicNonconstantEisenstein K hζ s q‖ -
    ‖sourceKPAdelicTraceIntertwiner K hζ s q‖)
  nlinarith [norm_nonneg (sourceKPAdelicNonconstantEisenstein K hζ s q +
    sourceKPAdelicTraceIntertwiner K hζ s q), norm_nonneg (sourceKPAdelicNonconstantEisenstein K hζ s q),
    norm_nonneg (sourceKPAdelicTraceIntertwiner K hζ s q)]

end
end ArtinMatthews
