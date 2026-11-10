module

public import ArtinMatthews.SourceKPArchFrame
public import ArtinMatthews.SourceKPArchCompactHaar
public import ArtinMatthews.SourceKPArchHyperbolicMeasure
public import ArtinMatthews.QuotientSectionMeasure
public import ArtinMatthews.QuotientSectionHaar
public import ArtinMatthews.QuotientSectionIntegral
public import ArtinMatthews.QuotientSectionRightMeasure
public import ArtinMatthews.SourceKPArithmeticDiscreteness
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

/-! The actual archimedean Haar measure, with hyperbolic quotient measure
and compact factor of mass one. -/
namespace ArtinMatthews
open NumberField Matrix Topology MeasureTheory
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local instance : MeasurableSpace (SourceKPArchSymmetricSpace K hζ) := borel _
local instance : BorelSpace (SourceKPArchSymmetricSpace K hζ) := ⟨rfl⟩

def sourceKPArchHaar : Measure (PGL(2, InfiniteAdeleRing K)) :=
  quotientSectionMeasure (sourceKPArchBaseCompactSubgroup K hζ)
    (sourceKPArchFrameSection K hζ) (sourceKPArchSymmetricHyperbolicMeasure K hζ)
    (sourceKPArchCompactHaar K hζ)

instance sourceKPArchHaar_isHaar : (sourceKPArchHaar K hζ).IsHaarMeasure :=
  quotientSectionMeasure_isHaar (sourceKPArchBaseCompactSubgroup K hζ)
    (sourceKPArchFrameSection K hζ) (sourceKPArchFrameSection_rightInverse K hζ)
    (sourceKPArchFrameSection_continuous K hζ)
    (sourceKPArchSymmetricHyperbolicMeasure K hζ) (sourceKPArchCompactHaar K hζ)
    (sourceKPArchSymmetricHyperbolicMeasure_preserving K hζ)

theorem sourceKPArchHaar_left_preserving (g : PGL(2, InfiniteAdeleRing K)) :
    MeasurePreserving (fun x => g*x) (sourceKPArchHaar K hζ) (sourceKPArchHaar K hζ) :=
  measurePreserving_mul_left (sourceKPArchHaar K hζ) g

theorem sourceKPArchHaar_right_compact_preserving (k : sourceKPArchBaseCompactSubgroup K hζ) :
    MeasurePreserving (fun x => x*k.val) (sourceKPArchHaar K hζ) (sourceKPArchHaar K hζ) :=
  quotientSectionMeasure_right_preserving (sourceKPArchBaseCompactSubgroup K hζ)
    (sourceKPArchFrameSection K hζ) (sourceKPArchFrameSection_rightInverse K hζ)
    (sourceKPArchFrameSection_continuous K hζ)
    (sourceKPArchSymmetricHyperbolicMeasure K hζ) (sourceKPArchCompactHaar K hζ) k

theorem sourceKPArchHaar_projection :
    MeasurePreserving (QuotientGroup.mk : PGL(2, InfiniteAdeleRing K) → SourceKPArchSymmetricSpace K hζ)
      (sourceKPArchHaar K hζ) (sourceKPArchSymmetricHyperbolicMeasure K hζ) :=
  quotientSectionMeasure_projection (sourceKPArchBaseCompactSubgroup K hζ)
    (sourceKPArchFrameSection K hζ) (sourceKPArchFrameSection_rightInverse K hζ)
    (sourceKPArchFrameSection_continuous K hζ)
    (sourceKPArchSymmetricHyperbolicMeasure K hζ) (sourceKPArchCompactHaar K hζ)

theorem sourceKPArchHaar_integral (f : PGL(2, InfiniteAdeleRing K) → ℂ)
    (hf : Integrable f (sourceKPArchHaar K hζ)) :
    (∫ g, f g ∂sourceKPArchHaar K hζ) =
      ∫ q, ∫ k : sourceKPArchBaseCompactSubgroup K hζ,
        f (sourceKPArchFrameSection K hζ q*k.val)
          ∂sourceKPArchCompactHaar K hζ ∂sourceKPArchSymmetricHyperbolicMeasure K hζ :=
  quotientSectionMeasure_integral (sourceKPArchBaseCompactSubgroup K hζ)
    (sourceKPArchFrameSection K hζ) (sourceKPArchFrameSection_continuous K hζ)
    (sourceKPArchSymmetricHyperbolicMeasure K hζ) (sourceKPArchCompactHaar K hζ) f hf

end
end ArtinMatthews
