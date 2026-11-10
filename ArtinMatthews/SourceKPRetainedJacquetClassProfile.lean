module

public import ArtinMatthews.SourceKPRetainedRowCharacterTensor
public import ArtinMatthews.SourceKPAdelicOutgoingRetainedJacquetProfile
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

/-! The actual retained Jacquet basis profiles retain their support and
exponent after the source theta, row, and sixth-class multipliers. -/
namespace ArtinMatthews

open NumberField IsDedekindDomain ClassFieldTheory QuadraticWeil
open VaryingKummerAnalytic SourcePhysical
open scoped NumberField Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12) (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
local notation "S" => sourceHilbertSet K S₀

theorem sourceKPRetainedJacquetClassProfile_data
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)
    {J : Ideal (𝓞 K)} (η : EvenIdealRayCharacter K J) (hJ : J ≠ ⊥)
    (u : exteriorUnitSubgroup (sourceHilbertSet K S₀)) (P : S) (hs : 0 < (1 / 6 : ℂ).re)
    (k : SourceKPAdelicOutgoingRetainedJacquetBasisIndex K hζ P.val hs)
    (a : SourceFiniteKP2Projective K hζ P.val)
    (r : PowerClassGroup (P.val.adicCompletion K) 6) :
    let χ := sourceKPRetainedFiniteRowCharacter K hζ S₀ hS η hJ u
    let V := sourceKPAdelicOutgoingRetainedJacquetBasisDiagonalProfile K hζ P.val hs k a
    let F := sourceKPRetainedLocalClassProfile K P.val (sourceKPRetainedFiniteCharacterAt K S χ P) r V
    Continuous F ∧ ∃ n : ℤ, ∃ A : ℝ, 0 < A ∧
      (∀ z : (P.val.adicCompletion K)ˣ, z ∉ sourceLocalMulBall K P.val n → F z = 0) ∧
      ∀ z : (P.val.adicCompletion K)ˣ, z ∈ sourceLocalMulBall K P.val 0 →
        ‖F z‖ ≤ A * ‖(z : P.val.adicCompletion K)‖ ^ (1 / 3 : ℝ) := by
  let χ := sourceKPRetainedFiniteRowCharacter K hζ S₀ hS η hJ u
  exact sourceKPRetainedLocalClassProfile_data K P.val _ r _
    (sourceKPRetainedFiniteCharacterAt_continuous K S χ
      (sourceKPRetainedFiniteRowCharacter_continuous K hζ S₀ hS η hJ u) P)
    (sourceKPRetainedFiniteCharacterAt_norm K S χ
      (sourceKPRetainedFiniteRowCharacter_norm K hζ S₀ hS η hJ u) P)
    (sourceKPAdelicOutgoingRetainedJacquetBasisDiagonalProfile_data K hζ P.val hs k a)

end
end ArtinMatthews
