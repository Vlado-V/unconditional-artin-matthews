module

public import ArtinMatthews.SourceSLocalSheetCoordinates
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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

/-! Logarithmic form of the forced positive radius on the actual sheet. -/

namespace ArtinMatthews.SourcePhysical
open NumberField NumberField.InfinitePlace IsDedekindDomain
open scoped NumberField
noncomputable section

variable {K : Type} [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K))) (v : InfinitePlace K)

theorem sourceSheetRadius_eq_exp (y : SNormOneOtherUnits S v) :
    sourceSheetRadius S v y = Real.exp (-Real.log (sourceSheetOtherNorm S v y) / 2) := by
  rw [sourceSheetRadius, ← Real.exp_log (inv_pos.mpr (sourceSheetOtherNorm_pos S v y)),
    ← Real.exp_half, Real.log_inv]

theorem sourceSheetRadius_log_sq (y : SNormOneOtherUnits S v) :
    Real.log (sourceSheetRadius S v y ^ 2) = -Real.log (sourceSheetOtherNorm S v y) := by
  rw [sourceSheetRadius_sq, Real.log_inv]

variable {v}

theorem sourceSNormOneFromSheet_chosen_log_sq (hv : IsComplex v)
    (y : Circle × SNormOneOtherUnits S v) :
    Real.log (‖((sourceSNormOneFromSheet hv S y).val.1 v : v.Completion)‖ ^ 2) =
      -Real.log (sourceSheetOtherNorm S v y.2) := by
  rw [sourceSNormOneFromSheet_chosen_norm, sourceSheetRadius_log_sq]

end
end ArtinMatthews.SourcePhysical
