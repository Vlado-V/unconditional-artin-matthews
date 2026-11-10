module

public import ArtinMatthews.SourceKPCompactC2Core
public import ArtinMatthews.SourceKPArchHaar
public import ArtinMatthews.SourceKPAutomorphicL2
public import ArtinMatthews.SourceKPAutomorphicCompactHaar
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

/-! Compact scalar tests have genuine mass in the canonical Haar L2 space. -/
namespace ArtinMatthews
open NumberField MeasureTheory
open scoped NumberField MatrixGroups AdeleRing ContDiff
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPCompactCore_memLp {n : ℕ∞ω} (f : sourceKPCompactCore K hζ n) :
    MemLp f.val 2 (sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)) := by
  let : IsFiniteMeasureOnCompacts
      (sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)) :=
    sourceKPAutomorphicCompactHaar_finiteOnCompacts K hζ
  exact f.prop.1.memLp_of_hasCompactSupport f.prop.2.1

def sourceKPCompactCoreMass (n : ℕ∞ω) : sourceKPCompactCore K hζ n →ₗ[ℂ]
    Lp ℂ 2 (sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)) where
  toFun f := (sourceKPCompactCore_memLp K hζ f).toLp f.val
  map_add' _f _g := MemLp.toLp_add _ _
  map_smul' c _f := MemLp.toLp_const_smul c _

theorem sourceKPCompactCoreMass_coe {n : ℕ∞ω} (f : sourceKPCompactCore K hζ n) :
    (sourceKPCompactCoreMass K hζ n f : SourceKPAutomorphicCompactLevel K hζ → ℂ) =ᵐ[
      sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)] f.val :=
  (sourceKPCompactCore_memLp K hζ f).coeFn_toLp

end
end ArtinMatthews
