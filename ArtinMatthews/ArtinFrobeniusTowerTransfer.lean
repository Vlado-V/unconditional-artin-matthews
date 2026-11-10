module

public import ArtinMatthews.ArtinFrobeniusIdealCharacter
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ArithmeticUnramifiedPrimeArtin
public import ArtinMatthews.ArtinFrobeniusConductorSupport
public import ArtinMatthews.ArtinRayPrimeComparison
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
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

/-! Restriction of actual Frobenius ideal characters in a finite abelian
tower. Equality is proved through the genuine global Artin map and the
actual unramified prime comparison, not supplied as a transfer premise. -/
namespace ArtinMatthews.VaryingKummerAnalytic.ArtinRay
open NumberField IsDedekindDomain
open GlobalClassFieldTheory.GlobalClassFields
open scoped NumberField nonZeroDivisors Classical
noncomputable section

variable {K E L : Type} [Field K] [NumberField K] [Field E] [NumberField E]
variable [Field L] [NumberField L] [Algebra K E] [Algebra E L] [Algebra K L]
variable [IsScalarTower K E L] [IsAbelianGalois K E] [IsAbelianGalois K L]

theorem arithmeticPrimeArtin_restrict_tower (v : HeightOneSpectrum (𝓞 K)) :
    AlgEquiv.restrictNormalHom E
      (arithmeticFinitePlacePrimeArtin (K := K) (L := L) v)=
      arithmeticFinitePlacePrimeArtin (K := K) (L := E) v := by
  rw [arithmeticFinitePlacePrimeArtin_eq_inv (K := K) (L := L) v,
    arithmeticFinitePlacePrimeArtin_eq_inv (K := K) (L := E) v,map_inv]
  simpa only [finitePlacePrimeArtin,MonoidHom.comp_apply] using
    congrArg Inv.inv (DFunLike.congr_fun
      (GlobalClassFieldTheory.Reciprocity.globalArtinMonoidHom_restrict_tower
        (K := K) (L := L) (E := E)) (IdeleGroup.finitePrimeIdele v))

theorem idealHom_prime_comp_restrict (χ : Gal(E/K) →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 K))
    (hL : Algebra.IsUnramifiedAt (𝓞 K) (GaloisIdealCharacter.primeAbove K L v).val)
    (hE : Algebra.IsUnramifiedAt (𝓞 K) (GaloisIdealCharacter.primeAbove K E v).val) :
    GaloisIdealCharacter.idealHom K L (χ.comp (AlgEquiv.restrictNormalHom E))
        (integralIdealFractionalUnit v.asIdeal v.ne_bot)=
      GaloisIdealCharacter.idealHom K E χ (integralIdealFractionalUnit v.asIdeal v.ne_bot) := by
  rw [idealHom_prime_arithmeticArtin _ v hL,idealHom_prime_arithmeticArtin _ v hE,
    MonoidHom.comp_apply,arithmeticPrimeArtin_restrict_tower]

theorem idealHom_comp_restrict_of_unramified_support (χ : Gal(E/K) →* ℂˣ)
    (I : FractionalIdealGroup K)
    (hL : ∀ v : HeightOneSpectrum (𝓞 K), FractionalIdeal.count K v I.val ≠ 0 →
      Algebra.IsUnramifiedAt (𝓞 K) (GaloisIdealCharacter.primeAbove K L v).val)
    (hE : ∀ v : HeightOneSpectrum (𝓞 K), FractionalIdeal.count K v I.val ≠ 0 →
      Algebra.IsUnramifiedAt (𝓞 K) (GaloisIdealCharacter.primeAbove K E v).val) :
    GaloisIdealCharacter.idealHom K L (χ.comp (AlgEquiv.restrictNormalHom E)) I=
      GaloisIdealCharacter.idealHom K E χ I := by
  unfold GaloisIdealCharacter.idealHom
  apply finprod_congr
  intro v
  by_cases hv : FractionalIdeal.count K v I.val=0
  · simp only [hv,zpow_zero]
  · have he := idealHom_prime_comp_restrict χ v (hL v hv) (hE v hv)
    rw [GaloisIdealCharacter.idealHom_prime,GaloisIdealCharacter.idealHom_prime] at he
    exact congrArg (fun z : ℂˣ => z ^ FractionalIdeal.count K v I.val) he

theorem idealHom_comp_restrict_of_discriminant_support (χ : Gal(E/K) →* ℂˣ)
    (I : FractionalIdealGroup K)
    (hI : ∀ v : HeightOneSpectrum (𝓞 K), FractionalIdeal.count K v I.val ≠ 0 →
      ((NumberField.discr L).natAbs : 𝓞 K) ∉ v.asIdeal) :
    GaloisIdealCharacter.idealHom K L (χ.comp (AlgEquiv.restrictNormalHom E)) I=
      GaloisIdealCharacter.idealHom K E χ I := by
  apply idealHom_comp_restrict_of_unramified_support χ I
  · intro v hv
    let Q := GaloisIdealCharacter.primeAbove K L v
    let : Q.val.IsPrime := Q.property.1
    exact unramified_of_absDiscr_not_mem K L v.asIdeal Q.val Q.property.2.over.symm (hI v hv)
  · intro v hv
    have hnot : ((NumberField.discr E).natAbs : 𝓞 K) ∉ v.asIdeal := by
      intro hm
      apply hI v hv
      have hd : (NumberField.discr E).natAbs ∣ (NumberField.discr L).natAbs :=
        Int.natAbs_dvd_natAbs.mpr (NumberField.discr_dvd_discr E L)
      obtain ⟨c,hc⟩ := hd
      rw [hc,Nat.cast_mul]
      exact v.asIdeal.mul_mem_right _ hm
    let Q := GaloisIdealCharacter.primeAbove K E v
    let : Q.val.IsPrime := Q.property.1
    exact unramified_of_absDiscr_not_mem K E v.asIdeal Q.val Q.property.2.over.symm hnot

end
end ArtinMatthews.VaryingKummerAnalytic.ArtinRay
