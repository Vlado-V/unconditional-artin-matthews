module

public import ArtinMatthews.SLocalNormOneGroup
public import ArtinMatthews.SourceFrequencyUnitTransversal
public import ArtinMatthews.SLocalSUnitIsolation
public import ArtinMatthews.SourceFrequencyUnitPart
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

/-! Identify distinct arithmetic S-unit sixth powers with their exact
diagonal subgroup in the norm-one quotient used for unfolding. -/
namespace ArtinMatthews.SourcePhysical

open NumberField IsDedekindDomain
open scoped NumberField Classical
noncomputable section
variable (F : Type) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

def sourceExteriorUnitToActualSUnit : exteriorUnitSubgroup S →* SUnitGroup (K := F) S where
  toFun u := ⟨u.val, fun P hP =>
    (sourceExteriorPrincipalValuation_eq_zero_iff F P u.val).mp (u.property P hP)⟩
  map_one' := rfl
  map_mul' _ _ := rfl

def sourceActualSUnitToExteriorUnit : SUnitGroup (K := F) S →* exteriorUnitSubgroup S where
  toFun u := ⟨u.val, fun P hP =>
    (sourceExteriorPrincipalValuation_eq_zero_iff F P u.val).mpr (u.property P hP)⟩
  map_one' := rfl
  map_mul' _ _ := rfl

def sourceExteriorUnitActualEquiv : exteriorUnitSubgroup S ≃* SUnitGroup (K := F) S :=
  { sourceExteriorUnitToActualSUnit F S with
    invFun := sourceActualSUnitToExteriorUnit F S
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

theorem sourceWholeDiagonal_injective : Function.Injective (sWholeDiagonal F S) := by
  intro u v h
  apply Units.ext
  apply NumberField.mixedEmbedding_injective F
  exact (sWholeMixed_diagonal F S u).symm.trans
    ((congrArg (sWholeMixed F S) h).trans (sWholeMixed_diagonal F S v))

def sourceExteriorSixthNormOneMap : SourceExteriorUnitSixthPowers S →* sNormOneSixthSubgroup F S :=
  ((sNormOneUnitMap F S).comp ((sourceExteriorUnitToActualSUnit F S).comp
    (SourceExteriorUnitSixthPowers S).subtype)).codRestrict (sNormOneSixthSubgroup F S) (by
      intro u
      obtain ⟨t, ht⟩ := sourceExteriorUnitSixthPower_exists_root S u
      refine ⟨sourceExteriorUnitToActualSUnit F S t, ?_⟩
      apply Subtype.ext
      rw [sNormOneSixthMap_val]
      change sWholeDiagonal F S ((t.val : Fˣ) ^ 6) = sWholeDiagonal F S u.val.val
      rw [ht]
      rfl)

theorem sourceExteriorSixthNormOneMap_val (u : SourceExteriorUnitSixthPowers S) :
    (sourceExteriorSixthNormOneMap F S u).val.val = sWholeDiagonal F S u.val.val := rfl

def sourceExteriorSixthNormOneEquiv : SourceExteriorUnitSixthPowers S ≃* sNormOneSixthSubgroup F S :=
  MulEquiv.ofBijective (sourceExteriorSixthNormOneMap F S) (by
    constructor
    · intro u v h
      have hd := congrArg (fun x : sNormOneSixthSubgroup F S => x.val.val) h
      rw [sourceExteriorSixthNormOneMap_val, sourceExteriorSixthNormOneMap_val] at hd
      exact Subtype.ext (Subtype.ext (sourceWholeDiagonal_injective F S hd))
    · intro v
      obtain ⟨u, hu⟩ := v.property
      let t := sourceActualSUnitToExteriorUnit F S u
      let w : SourceExteriorUnitSixthPowers S := ⟨t ^ 6, ⟨t, rfl⟩⟩
      refine ⟨w, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      have hv := congrArg (fun x : SNormOne F S => x.val) hu
      rw [sNormOneSixthMap_val] at hv
      rw [sourceExteriorSixthNormOneMap_val]
      exact hv)

theorem sourceExteriorSixthNormOneEquiv_val (u : SourceExteriorUnitSixthPowers S) :
    (sourceExteriorSixthNormOneEquiv F S u).val.val = sWholeDiagonal F S u.val.val := rfl

end
end ArtinMatthews.SourcePhysical
