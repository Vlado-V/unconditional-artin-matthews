module

public import ArtinMatthews.KummerRowRayCharacters
public import ArtinMatthews.SixthExteriorPowerClassesQuotient
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
public import Mathlib.RingTheory.Henselian
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

/-! The actual Hecke coefficient map on reduced exterior sixth-power
classes. Its injectivity is derived from Kummer fixed fields, arithmetic
Frobenius faithfulness and the genuine exterior valuation calculation. -/
namespace ArtinMatthews
open NumberField VaryingKummerAnalytic IsDedekindDomain
open scoped NumberField nonZeroDivisors Classical
noncomputable section

theorem field_sixthPower_ratio_iff_unit {F : Type*} [Field F] (u v : Fˣ) :
    (∃ t : F, t^6 = (u:F)/(v:F)) ↔ ∃ t : Fˣ, u/v = t^6 := by
  constructor
  · rintro ⟨t,ht⟩
    have ht0 : t ≠ 0 := by
      intro hz
      rw [hz,zero_pow (by decide : 6 ≠ 0)] at ht
      exact (div_ne_zero u.ne_zero v.ne_zero) ht.symm
    refine ⟨Units.mk0 t ht0,?_⟩
    apply Units.ext
    simpa only [Units.val_div_eq_div_val,Units.val_pow_eq_pow_val,Units.val_mk0] using ht.symm
  · rintro ⟨t,ht⟩
    refine ⟨(t:F),?_⟩
    simpa only [Units.val_div_eq_div_val,Units.val_pow_eq_pow_val] using
      (congrArg (fun x : Fˣ => (x:F)) ht).symm

variable {F : Type} [Field F] [NumberField F] [Algebra F ℂ]
variable [NumberField.IsTotallyComplex F]

def sixthUnitRowParameters (A : Finset Fˣ) : Finset F := A.image (fun u : Fˣ => (u:F))

def sixthUnitRowRayCharacter {ζ : F} (hζ : IsPrimitiveRoot ζ 6)
    (A : Finset Fˣ) (u : {u // u ∈ A}) :
    EvenRayCharacter F (discriminantDegreeModulus F
      (sixthKummerRowField (sixthUnitRowParameters A))) :=
  sixthKummerRowRayCharacter hζ (sixthUnitRowParameters A) (u.val:F)
    (by simpa only [sixthUnitRowParameters] using
      (Finset.mem_image_of_mem (fun v : Fˣ => (v:F)) u.property)) u.val.ne_zero

theorem sixthUnitRowRayCharacter_coefficient_eq_iff {ζ : F} (hζ : IsPrimitiveRoot ζ 6)
    (A : Finset Fˣ) (u v : {u // u ∈ A}) :
    (sixthUnitRowRayCharacter hζ A u).coefficient =
      (sixthUnitRowRayCharacter hζ A v).coefficient ↔ ∃ t : Fˣ, u.val/v.val=t^6 := by
  change (sixthKummerRowRayCharacter hζ (sixthUnitRowParameters A) (u.val:F) _ _).coefficient =
    (sixthKummerRowRayCharacter hζ (sixthUnitRowParameters A) (v.val:F) _ _).coefficient ↔ _
  rw [sixthKummerRowRayCharacter_coefficient_eq_iff,field_sixthPower_ratio_iff_unit]

def finiteExteriorRowSetoid (S : Finset (HeightOneSpectrum (𝓞 F))) (A : Finset Fˣ) :
    Setoid {u // u ∈ A} where
  r u v := QuotientGroup.mk' (exteriorSixthPowerSubgroup S) u.val =
    QuotientGroup.mk' (exteriorSixthPowerSubgroup S) v.val
  iseqv := ⟨fun _ => rfl,fun h => h.symm,fun h₁ h₂ => h₁.trans h₂⟩

theorem sixthUnitRowRayCharacter_coefficient_eq_iff_exterior {ζ : F}
    (hζ : IsPrimitiveRoot ζ 6) (S : Finset (HeightOneSpectrum (𝓞 F))) (A : Finset Fˣ)
    (hA : ∀ u ∈ A, ExteriorSixthReduced S u) (u v : {u // u ∈ A}) :
    (sixthUnitRowRayCharacter hζ A u).coefficient =
      (sixthUnitRowRayCharacter hζ A v).coefficient ↔ (finiteExteriorRowSetoid S A).r u v := by
  rw [sixthUnitRowRayCharacter_coefficient_eq_iff]
  change (∃ t : Fˣ, u.val/v.val=t^6) ↔
    ((u.val : Fˣ ⧸ exteriorSixthPowerSubgroup S) = v.val)
  rw [QuotientGroup.eq_iff_div_mem,mem_exteriorSixthPowerSubgroup]
  exact (exteriorSixthReduced_power_iff S u.val v.val (hA u.val u.property) (hA v.val v.property)).trans
    ⟨fun ⟨t,ht⟩ => ⟨t,ht.symm⟩,fun ⟨t,ht⟩ => ⟨t,ht.symm⟩⟩

def reducedKummerCoefficientMap {ζ : F} (hζ : IsPrimitiveRoot ζ 6)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (A : Finset Fˣ)
    (hA : ∀ u ∈ A, ExteriorSixthReduced S u) :
    Quotient (finiteExteriorRowSetoid S A) → (integralFractionalIdeals F → ℂ) :=
  Quotient.lift (fun u => (sixthUnitRowRayCharacter hζ A u).coefficient)
    (fun u v h => (sixthUnitRowRayCharacter_coefficient_eq_iff_exterior hζ S A hA u v).mpr h)

theorem reducedKummerCoefficientMap_mk {ζ : F} (hζ : IsPrimitiveRoot ζ 6)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (A : Finset Fˣ)
    (hA : ∀ u ∈ A, ExteriorSixthReduced S u) (u : {u // u ∈ A}) :
    reducedKummerCoefficientMap hζ S A hA (Quotient.mk (finiteExteriorRowSetoid S A) u) =
      (sixthUnitRowRayCharacter hζ A u).coefficient := rfl

theorem reducedKummerCoefficientMap_injective {ζ : F} (hζ : IsPrimitiveRoot ζ 6)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (A : Finset Fˣ)
    (hA : ∀ u ∈ A, ExteriorSixthReduced S u) :
    Function.Injective (reducedKummerCoefficientMap hζ S A hA) := by
  intro a b
  refine Quotient.inductionOn₂ a b ?_
  intro u v h
  apply Quotient.sound
  exact (sixthUnitRowRayCharacter_coefficient_eq_iff_exterior hζ S A hA u v).mp h

end
end ArtinMatthews
