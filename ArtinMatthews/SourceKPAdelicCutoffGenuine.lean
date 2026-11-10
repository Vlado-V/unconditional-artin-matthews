module

public import ArtinMatthews.SourceKPAdelicCuspCutoff
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

/-! The actual cubic central character of the global cusp cutoff. -/

namespace ArtinMatthews
open NumberField
open scoped NumberField
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAdelicCoverHeight_center (z : rootsOfUnity 3 K)
    (q : SourceKPAdelicProjective K hζ) :
    sourceKPAdelicCoverHeight K hζ (sourceKPAdelicProjectiveCenter K hζ z*q) =
      sourceKPAdelicCoverHeight K hζ q := by
  unfold sourceKPAdelicCoverHeight
  rw [map_mul,sourceKPAdelicProjectiveCenter_projection_one,one_mul]

theorem sourceKPAdelicCutoffSeed_center (T : ℝ) (s : ℂ) (z : rootsOfUnity 3 K)
    (q : SourceKPAdelicProjective K hζ) :
    (sourceKPAdelicCutoffSeed K hζ T s).val (sourceKPAdelicProjectiveCenter K hζ z*q) =
      (sourceKPAdelicCentralComplex K hζ z : ℂ)*(sourceKPAdelicCutoffSeed K hζ T s).val q := by
  change (sourceKPAdelicHeightCutoff T (sourceKPAdelicCoverHeight K hζ
      (sourceKPAdelicProjectiveCenter K hζ z*q)) : ℂ) *
        sourceKPAdelicCompactScalar K hζ s (sourceKPAdelicProjectiveCenter K hζ z*q) = _
  rw [sourceKPAdelicCoverHeight_center]
  have he := sourceKPAdelicPrincipalSeriesScalar_center K hζ s (sourceKPAdelicCompactSection K hζ s) z q
  change sourceKPAdelicCompactScalar K hζ s (sourceKPAdelicProjectiveCenter K hζ z*q) =
    (sourceKPAdelicCentralComplex K hζ z : ℂ)*sourceKPAdelicCompactScalar K hζ s q at he
  rw [he]
  change _ * (_ * _) = _ * (_ * _)
  ring

theorem sourceKPAdelicCutoffEisenstein_center (T : ℝ) (s : ℂ) (z : rootsOfUnity 3 K)
    (q : SourceKPAdelicProjective K hζ) :
    sourceKPAdelicCutoffEisenstein K hζ T s (sourceKPAdelicProjectiveCenter K hζ z*q) =
      (sourceKPAdelicCentralComplex K hζ z : ℂ)*sourceKPAdelicCutoffEisenstein K hζ T s q :=
  sourceKPAdelicRationalSum_genuine K hζ (sourceKPAdelicCutoffSeed K hζ T s)
    (sourceKPAdelicCutoffSeed_center K hζ T s) z q

end
end ArtinMatthews
