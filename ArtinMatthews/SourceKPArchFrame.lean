module

public import ArtinMatthews.SourceKPArchGramQuotient
public import ArtinMatthews.QuotientSectionFrame
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

/-! The actual archimedean group frame from its Gram section and compact factor. -/
namespace ArtinMatthews
open NumberField Matrix Topology
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPArchFrameSection (q : SourceKPArchSymmetricSpace K hζ) :
    PGL(2, InfiniteAdeleRing K) :=
  ProjGenLinGroup.mk (sourceKPArchUpperHalfSection K hζ
    (sourceKPArchSymmetricHomeomorph K hζ q))

theorem sourceKPArchFrameSection_rightInverse (q : SourceKPArchSymmetricSpace K hζ) :
    QuotientGroup.mk (sourceKPArchFrameSection K hζ q) = q :=
  sourceKPArchSymmetricSection_coordinates K hζ q

theorem sourceKPArchFrameSection_continuous : Continuous (sourceKPArchFrameSection K hζ) :=
  QuotientGroup.continuous_mk.comp ((sourceKPArchUpperHalfSection_continuous K hζ).comp
    (sourceKPArchSymmetricHomeomorph K hζ).continuous)

def sourceKPArchFrameHomeomorph :
    PGL(2, InfiniteAdeleRing K) ≃ₜ
      (SourceKPArchUpperHalfSpace K × sourceKPArchBaseCompactSubgroup K hζ) :=
  (quotientSectionFrameHomeomorph (sourceKPArchBaseCompactSubgroup K hζ)
    (sourceKPArchFrameSection K hζ) (sourceKPArchFrameSection_rightInverse K hζ)
    (sourceKPArchFrameSection_continuous K hζ)).trans
      ((sourceKPArchSymmetricHomeomorph K hζ).prodCongr (Homeomorph.refl _))

theorem sourceKPArchFrameHomeomorph_fst (g : PGL(2, InfiniteAdeleRing K)) :
    (sourceKPArchFrameHomeomorph K hζ g).1 = sourceKPArchGramCoordinates K hζ g := rfl

end
end ArtinMatthews
