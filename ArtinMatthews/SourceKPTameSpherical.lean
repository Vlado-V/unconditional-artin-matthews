module

public import ArtinMatthews.SourceKPTameBorelCompact
public import ArtinMatthews.SourceAlgebraicInduction
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

/-! The actual algebraic normalized induction and its distinguished
spherical section on the local projective cubic cover. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain
open scoped NumberField
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K)) (h6 : (6 : 𝓞 K) ∉ P.asIdeal)
    (π : (P.adicCompletion K)ˣ)
    (hπ : sourceKPFiniteVal K P (π : P.adicCompletion K) = WithZero.exp (-1 : ℤ))

abbrev sourceKPTameInducedSpace :=
  sourceAlgebraicInducedSpace (sourceFiniteKPNormalizedBorelToProjective K hζ P).range
    (sourceKPTameBorelRepresentation K hζ P h6 π hπ)

def sourceKPTameInducedRepresentation :
    Representation ℂ (SourceFiniteKP2Projective K hζ P) (sourceKPTameInducedSpace K hζ P h6 π hπ) :=
  sourceAlgebraicInducedRepresentation (sourceFiniteKPNormalizedBorelToProjective K hζ P).range
    (sourceKPTameBorelRepresentation K hζ P h6 π hπ)

def sourceKPTameSphericalSection : sourceKPTameInducedSpace K hζ P h6 π hπ :=
  sourceAlgebraicSphericalSection (sourceFiniteKPNormalizedBorelToProjective K hζ P).range
    (sourceKPTameBorelRepresentation K hζ P h6 π hπ)
    (sourceFiniteKP2ProjectiveCompactSection K hζ P h6).range (sourceJacquetBasis 0)
    (sourceFiniteKP2Projective_Iwasawa_range K hζ P h6)
    (sourceKPTameBorelRepresentation_compact_fixed K hζ P h6 π hπ)

theorem sourceKPTameSphericalSection_covariant (b : SourceFiniteKPProjectiveBorel K hζ P)
    (g : SourceFiniteKP2Projective K hζ P) :
    (sourceKPTameSphericalSection K hζ P h6 π hπ).val (b.val * g) =
      sourceKPTameBorelRepresentation K hζ P h6 π hπ b
        ((sourceKPTameSphericalSection K hζ P h6 π hπ).val g) :=
  (sourceKPTameSphericalSection K hζ P h6 π hπ).property b g

theorem sourceKPTameSphericalSection_factor {g : SourceFiniteKP2Projective K hζ P}
    (b : SourceFiniteKPProjectiveBorel K hζ P) (k : SourceFiniteKP2Integral K P)
    (hg : g = b.val * sourceFiniteKP2ProjectiveCompactSection K hζ P h6 k) :
    (sourceKPTameSphericalSection K hζ P h6 π hπ).val g =
      sourceKPTameBorelRepresentation K hζ P h6 π hπ b (sourceJacquetBasis 0) := by
  let c : SourceFiniteKP2ProjectiveCompact K hζ P h6 :=
    ⟨sourceFiniteKP2ProjectiveCompactSection K hζ P h6 k, ⟨k, rfl⟩⟩
  exact sourceAlgebraicSphericalSection_factor _ _ _ _ _ _ (b := b) (c := c) hg

theorem sourceKPTameSphericalSection_one :
    (sourceKPTameSphericalSection K hζ P h6 π hπ).val 1 = sourceJacquetBasis 0 :=
  sourceAlgebraicSphericalSection_one _ _ _ _ _ _

theorem sourceKPTameSphericalSection_compact (k : SourceFiniteKP2Integral K P) :
    (sourceKPTameSphericalSection K hζ P h6 π hπ).val
      (sourceFiniteKP2ProjectiveCompactSection K hζ P h6 k) = sourceJacquetBasis 0 := by
  rw [sourceKPTameSphericalSection_factor K hζ P h6 π hπ 1 k (one_mul _).symm, map_one]
  rfl

theorem sourceKPTameSphericalSection_right (k : SourceFiniteKP2Integral K P) :
    sourceKPTameInducedRepresentation K hζ P h6 π hπ (sourceFiniteKP2ProjectiveCompactSection K hζ P h6 k)
      (sourceKPTameSphericalSection K hζ P h6 π hπ) = sourceKPTameSphericalSection K hζ P h6 π hπ := by
  let c : SourceFiniteKP2ProjectiveCompact K hζ P h6 :=
    ⟨sourceFiniteKP2ProjectiveCompactSection K hζ P h6 k, ⟨k, rfl⟩⟩
  exact sourceAlgebraicSphericalSection_right _ _ _ _ _ _ c

end
end ArtinMatthews
