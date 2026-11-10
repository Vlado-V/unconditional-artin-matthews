module

public import ArtinMatthews.SixthExteriorIdealRows
public import ArtinMatthews.KummerReducedRowCharacters
public import ArtinMatthews.SixthExteriorPowerClassesFinite
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Int.Star
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Basify
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

/-! Literal bounded ideal/S-unit rows with a proved injective map to
global sixth-power classes and actual Frobenius coefficient functions. -/
namespace ArtinMatthews
open IsDedekindDomain VaryingKummerAnalytic
open scoped NumberField Classical
noncomputable section

variable {K : Type} [Field K] [NumberField K]

abbrev ExteriorIdealRowIndex (S : Finset (HeightOneSpectrum (𝓞 K))) (N : ℕ) :=
  {I // I ∈ exteriorBoundedIdealRows S N} ×
    {r : exteriorUnitSubgroup S // r ∈ exteriorUnitSixthRepresentatives S}

theorem exteriorIdealRowIndex_card (S : Finset (HeightOneSpectrum (𝓞 K))) (N : ℕ) :
    Fintype.card (ExteriorIdealRowIndex S N)=
      (exteriorBoundedIdealRows S N).card*(exteriorUnitSixthRepresentatives S).card := by
  simp only [ExteriorIdealRowIndex,Fintype.card_prod,Fintype.card_coe]

def exteriorBoundedIdealRowUnit (S : Finset (HeightOneSpectrum (𝓞 K))) (N : ℕ)
    (i : ExteriorIdealRowIndex S N) : Kˣ :=
  exteriorIdealRow S i.1.1 ((mem_exteriorBoundedIdealRows S N i.1.1).mp i.1.2).2.1 i.2.1

theorem exteriorBoundedIdealRowUnit_reduced
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hS : exteriorPrincipalizingPrimes K ⊆ S)
    (N : ℕ) (i : ExteriorIdealRowIndex S N) :
    ExteriorSixthReduced S (exteriorBoundedIdealRowUnit S N i) :=
  exteriorIdealRow_reduced S hS N i.1.1 i.1.2 i.2.1

def exteriorBoundedIdealRowClass (S : Finset (HeightOneSpectrum (𝓞 K))) (N : ℕ)
    (i : ExteriorIdealRowIndex S N) : Kˣ ⧸ globalSixthPowerSubgroup :=
  QuotientGroup.mk' globalSixthPowerSubgroup (exteriorBoundedIdealRowUnit S N i)

/-- The ideal and the finite S-unit class are both recovered from a
global sixth-power class. No row injectivity is assumed. -/
theorem exteriorBoundedIdealRowClass_injective
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hS : exteriorPrincipalizingPrimes K ⊆ S)
    (N : ℕ) : Function.Injective (exteriorBoundedIdealRowClass S N) := by
  rintro ⟨⟨I,hI⟩,⟨r,hr⟩⟩ ⟨⟨J,hJ⟩,⟨s,hs⟩⟩ h
  have hm : exteriorBoundedIdealRowUnit S N (⟨I,hI⟩,⟨r,hr⟩) /
      exteriorBoundedIdealRowUnit S N (⟨J,hJ⟩,⟨s,hs⟩) ∈ globalSixthPowerSubgroup :=
    QuotientGroup.eq_iff_div_mem.mp h
  obtain ⟨t,ht⟩ := (mem_globalSixthPowerSubgroup _).mp hm
  have hIJ := exteriorIdealRow_ideal_eq_of_sixthPower S hS N I J hI hJ r s t ht.symm
  subst J
  have hratio : (r:Kˣ)/(s:Kˣ)=t^6 := by
    change t^6=(exteriorIdealGenerator I _ * (r:Kˣ)) /
      (exteriorIdealGenerator I _ * (s:Kˣ)) at ht
    simpa only [mul_div_mul_left_eq_div] using ht.symm
  have hrr : ExteriorSixthReduced S (r:Kˣ) := by
    intro p hp
    rw [r.2 p hp]
    norm_num
  have hss : ExteriorSixthReduced S (s:Kˣ) := by
    intro p hp
    rw [s.2 p hp]
    norm_num
  have htS := (exteriorSixthReduced_ratio_root S r s t hrr hss hratio).2
  let z : exteriorUnitSubgroup S := ⟨t,htS⟩
  have hdiv : r/s=z^6 := Subtype.ext hratio
  have hclass : QuotientGroup.mk' (powMonoidHom (α := exteriorUnitSubgroup S) 6).range r=
      QuotientGroup.mk' (powMonoidHom (α := exteriorUnitSubgroup S) 6).range s :=
    QuotientGroup.eq_iff_div_mem.mpr ⟨z,hdiv.symm⟩
  have hrs := exteriorUnitSixthRepresentatives_unique S hr hs hclass
  subst s
  rfl

def exteriorBoundedIdealRowUnits (S : Finset (HeightOneSpectrum (𝓞 K))) (N : ℕ) :
    Finset Kˣ := Finset.univ.image (exteriorBoundedIdealRowUnit S N)

theorem exteriorBoundedIdealRowUnits_card
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hS : exteriorPrincipalizingPrimes K ⊆ S)
    (N : ℕ) :
    (exteriorBoundedIdealRowUnits S N).card=
      (exteriorBoundedIdealRows S N).card*(exteriorUnitSixthRepresentatives S).card := by
  have hinj : Function.Injective (exteriorBoundedIdealRowUnit S N) := by
    intro i j hij
    apply exteriorBoundedIdealRowClass_injective S hS N
    exact congrArg (QuotientGroup.mk' globalSixthPowerSubgroup) hij
  rw [exteriorBoundedIdealRowUnits,Finset.card_image_of_injective _ hinj,
    Finset.card_univ,exteriorIdealRowIndex_card]

theorem exteriorBoundedIdealRowUnit_mem
    (S : Finset (HeightOneSpectrum (𝓞 K))) (N : ℕ) (i : ExteriorIdealRowIndex S N) :
    exteriorBoundedIdealRowUnit S N i ∈ exteriorBoundedIdealRowUnits S N :=
  Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩

variable [Algebra K ℂ] [NumberField.IsTotallyComplex K]

def exteriorBoundedIdealRowRayCharacter {ζ : K} (hζ : IsPrimitiveRoot ζ 6)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (N : ℕ) (i : ExteriorIdealRowIndex S N) :
    EvenRayCharacter K (discriminantDegreeModulus K
      (sixthKummerRowField (sixthUnitRowParameters (exteriorBoundedIdealRowUnits S N)))) :=
  sixthUnitRowRayCharacter hζ (exteriorBoundedIdealRowUnits S N)
    ⟨exteriorBoundedIdealRowUnit S N i,exteriorBoundedIdealRowUnit_mem S N i⟩

theorem exteriorBoundedIdealRowRayCharacter_coefficient_injective {ζ : K}
    (hζ : IsPrimitiveRoot ζ 6) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : exteriorPrincipalizingPrimes K ⊆ S) (N : ℕ) :
    Function.Injective (fun i : ExteriorIdealRowIndex S N =>
      (exteriorBoundedIdealRowRayCharacter hζ S N i).coefficient) := by
  intro i j hij
  have he := (sixthUnitRowRayCharacter_coefficient_eq_iff hζ (exteriorBoundedIdealRowUnits S N)
    ⟨exteriorBoundedIdealRowUnit S N i,exteriorBoundedIdealRowUnit_mem S N i⟩
    ⟨exteriorBoundedIdealRowUnit S N j,exteriorBoundedIdealRowUnit_mem S N j⟩).mp hij
  apply exteriorBoundedIdealRowClass_injective S hS N
  obtain ⟨t,ht⟩ := he
  exact QuotientGroup.eq_iff_div_mem.mpr ⟨t,ht.symm⟩

end
end ArtinMatthews
