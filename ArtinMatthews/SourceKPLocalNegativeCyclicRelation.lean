module

public import ArtinMatthews.SourceKPTameCyclicWhittaker
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

/-! The zero relation in the whole negative cyclic representation, with
its literal translation vectors and complex coefficients. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory StandardAdelic SourcePhysical QuadraticWeil
open scoped NumberField AdeleRing Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : SourceExteriorPrime K S₀)

local notation "G₀" => SourceFiniteKP2Projective K hζ P.val
local notation "C₋" => sourceKPTameSphericalCyclicSpace K hζ S₀ P
local notation "r₋" => sourceKPTameSphericalCyclicRepresentation K hζ S₀ P
local notation "v₋" => sourceKPTameCyclicSphericalVector K hζ S₀ P

def SourceKPLocalNegativeCyclicRelation {I : Type*} [Fintype I] (g : I → G₀) (c : I → ℂ) : Prop :=
  (∑ i, c i • r₋ (g i) v₋ : C₋) = 0

theorem sourceKPLocalNegativeCyclicRelation_iff {I : Type*} [Fintype I] (g : I → G₀) (c : I → ℂ) :
    SourceKPLocalNegativeCyclicRelation K hζ S₀ P g c ↔ (∑ i, c i • r₋ (g i) v₋ : C₋) = 0 :=
  Iff.rfl

end
end ArtinMatthews
