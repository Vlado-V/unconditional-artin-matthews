module

public import ArtinMatthews.SLocalNormOneGroup
public import ArtinMatthews.SourceReflectionWholeThetaCharacter
public import ArtinMatthews.SourceFrequencyNormOneAction
public import ArtinMatthews.SourceReflectionThetaDiagonal
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The reflected whole phase is trivial on the actual diagonal S-units,
including the original norm-one sixth-power subgroup. -/
namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField IsDedekindDomain AngularLambda AllowedGenerators SourcePhysical QuadraticWeil
open scoped NumberField Classical

noncomputable section

variable (F : Type) [Field F] [NumberField F]

theorem sourceReflectionExteriorIdele_fractionalIdeal_sUnit
    (T : Finset (HeightOneSpectrum (𝓞 F))) (u : SUnitGroup (K := F) T) :
    IdeleGroup.fractionalIdeal (sourceReflectionExteriorIdele F T u.val) = 1 := by
  rw [← MonoidHom.mem_ker, IdeleGroup.fractionalIdeal_ker]
  intro P
  change (sourceReflectionExteriorIdele F T u.val).2 P ∈ (P.adicCompletionIntegers F).units
  by_cases hP : P ∈ T
  · rw [sourceReflectionExteriorIdele_apply_mem F T u.val P hP]
    exact (P.adicCompletionIntegers F).units.one_mem
  · rw [sourceReflectionExteriorIdele_apply_notMem F T u.val P hP,
      HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one]
    change Valued.v ((u.val : F) : P.adicCompletion F) = 1
    rw [P.valuedAdicCompletion_eq_valuation']
    exact u.property P hP

variable [IsTotallyComplex F] {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
local notation "S" => sourceHilbertSet F S₀
variable {J : Ideal (𝓞 F)}

theorem sourceReflectionWholeThetaCharacter_diagonal_sUnit
    (hBad : standardWeilBadPlaces F ⊆ S) (η : EvenIdealRayCharacter F J) (hJ : J ≠ ⊥)
    (hcut : principalAngularCutoff F J ⊆ S) (u : SUnitGroup (K := F) S) :
    sourceReflectionWholeThetaCharacter F hζ S₀ hBad η hJ (sWholeDiagonal F S u.val) = 1 := by
  rw [sourceReflectionWholeThetaCharacter_diagonal F hζ S₀ hBad η hJ hcut u.val]
  rw [sourceReflectionExteriorIdele_fractionalIdeal_sUnit F S u]
  simp only [map_one, inv_one, mul_one]

theorem sourceReflectionWholeThetaCharacter_sixth
    (hBad : standardWeilBadPlaces F ⊆ S) (η : EvenIdealRayCharacter F J) (hJ : J ≠ ⊥)
    (hcut : principalAngularCutoff F J ⊆ S) (γ : sNormOneSixthSubgroup F S) :
    sourceReflectionWholeThetaCharacter F hζ S₀ hBad η hJ γ.val.val = 1 := by
  let u := (sourceExteriorSixthNormOneEquiv F S).symm γ
  let r := sourceExteriorUnitToActualSUnit F S u.val
  have h : (sourceExteriorSixthNormOneEquiv F S u).val.val = γ.val.val :=
    congrArg (fun x : sNormOneSixthSubgroup F S => x.val.val)
      ((sourceExteriorSixthNormOneEquiv F S).apply_symm_apply γ)
  rw [sourceExteriorSixthNormOneEquiv_val] at h
  change sWholeDiagonal F S r.val = γ.val.val at h
  rw [← h]
  exact sourceReflectionWholeThetaCharacter_diagonal_sUnit F hζ S₀ hBad η hJ hcut r

end
end ArtinMatthews.VaryingKummerAnalytic
