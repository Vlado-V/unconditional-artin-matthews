module

public import ArtinMatthews.SixthPrincipalRowCorrection


set_option backward.privateInPublic true
@[expose] public section

/-! Normalize the existing bounded ideal rows by one fixed S-unit sixth
power. The row index and its ideal norm are unchanged; the principal row
is literally 1, and all other rows are not sixth powers. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain
open scoped NumberField nonZeroDivisors Classical
noncomputable section
variable {K : Type} [Field K] [NumberField K]

theorem unitIdealRow_mem (S : Finset (HeightOneSpectrum (𝓞 K))) (N : ℕ) (hN : 1 ≤ N) :
    (1 : Ideal (𝓞 K)) ∈ exteriorBoundedIdealRows S N := by
  apply (mem_exteriorBoundedIdealRows S N 1).mpr
  refine ⟨by simpa using hN,one_ne_zero,?_,?_⟩
  · intro p _
    simpa only [Ideal.one_eq_top,FractionalIdeal.coeIdeal_top] using FractionalIdeal.count_one K p
  · intro p
    rw [Ideal.one_eq_top,FractionalIdeal.coeIdeal_top,FractionalIdeal.count_one]
    norm_num

def normalizedPrincipalRowIndex (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : exteriorPrincipalizingPrimes K ⊆ S) (N : ℕ) (hN : 1 ≤ N) : ExteriorIdealRowIndex S N :=
  (⟨1,unitIdealRow_mem S N hN⟩,
    ⟨(principalRowNormalizer S hS).representative,(principalRowNormalizer S hS).representative_mem⟩)

theorem normalizedPrincipalRowIndex_old_unit (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : exteriorPrincipalizingPrimes K ⊆ S) (N : ℕ) (hN : 1 ≤ N) :
    exteriorBoundedIdealRowUnit S N (normalizedPrincipalRowIndex S hS N hN) =
      principalRowCorrection S hS := (principalRowCorrection_eq_generator S hS).symm

def normalizedExteriorIdealRowUnit (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : exteriorPrincipalizingPrimes K ⊆ S) (N : ℕ) (i : ExteriorIdealRowIndex S N) : Kˣ :=
  exteriorBoundedIdealRowUnit S N i / principalRowCorrection S hS

theorem normalizedExteriorIdealRowUnit_principal (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : exteriorPrincipalizingPrimes K ⊆ S) (N : ℕ) (hN : 1 ≤ N) :
    normalizedExteriorIdealRowUnit S hS N (normalizedPrincipalRowIndex S hS N hN) = 1 := by
  rw [normalizedExteriorIdealRowUnit,normalizedPrincipalRowIndex_old_unit]
  exact div_self' _

theorem normalizedExteriorIdealRowUnit_valuation (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : exteriorPrincipalizingPrimes K ⊆ S) (N : ℕ) (i : ExteriorIdealRowIndex S N)
    (p : HeightOneSpectrum (𝓞 K)) (hp : p ∉ S) :
    exteriorPrincipalValuation p (normalizedExteriorIdealRowUnit S hS N i) =
      exteriorPrincipalValuation p (exteriorBoundedIdealRowUnit S N i) := by
  rw [normalizedExteriorIdealRowUnit,exteriorPrincipalValuation_div,
    principalRowCorrection_valuation S hS p hp,sub_zero]

theorem normalizedExteriorIdealRowUnit_reduced (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : exteriorPrincipalizingPrimes K ⊆ S) (N : ℕ) (i : ExteriorIdealRowIndex S N) :
    ExteriorSixthReduced S (normalizedExteriorIdealRowUnit S hS N i) := by
  intro p hp
  rw [normalizedExteriorIdealRowUnit_valuation S hS N i p hp]
  exact exteriorBoundedIdealRowUnit_reduced S hS N i p hp

def normalizedExteriorIdealRowClass (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : exteriorPrincipalizingPrimes K ⊆ S) (N : ℕ) (i : ExteriorIdealRowIndex S N) :
    Kˣ ⧸ globalSixthPowerSubgroup :=
  QuotientGroup.mk' globalSixthPowerSubgroup (normalizedExteriorIdealRowUnit S hS N i)

theorem normalizedExteriorIdealRowClass_eq (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : exteriorPrincipalizingPrimes K ⊆ S) (N : ℕ) (i : ExteriorIdealRowIndex S N) :
    normalizedExteriorIdealRowClass S hS N i = exteriorBoundedIdealRowClass S N i := by
  rw [normalizedExteriorIdealRowClass,normalizedExteriorIdealRowUnit,map_div,
    principalRowCorrection_class,div_one]
  rfl

theorem normalizedExteriorIdealRowClass_injective (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : exteriorPrincipalizingPrimes K ⊆ S) (N : ℕ) :
    Function.Injective (normalizedExteriorIdealRowClass S hS N) := by
  intro i j h
  apply exteriorBoundedIdealRowClass_injective S hS N
  simpa only [normalizedExteriorIdealRowClass_eq] using h

theorem normalizedExteriorIdealRowUnit_injective (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : exteriorPrincipalizingPrimes K ⊆ S) (N : ℕ) :
    Function.Injective (normalizedExteriorIdealRowUnit S hS N) := by
  intro i j h
  apply normalizedExteriorIdealRowClass_injective S hS N
  exact congrArg (QuotientGroup.mk' globalSixthPowerSubgroup) h

theorem normalizedExteriorIdealRow_sixthPower_iff (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : exteriorPrincipalizingPrimes K ⊆ S) (N : ℕ) (hN : 1 ≤ N) (i : ExteriorIdealRowIndex S N) :
    (∃ t : K, t^6=(normalizedExteriorIdealRowUnit S hS N i : K)) ↔
      i = normalizedPrincipalRowIndex S hS N hN := by
  have h := field_sixthPower_ratio_iff_unit
    (normalizedExteriorIdealRowUnit S hS N i) (1 : Kˣ)
  simp only [Units.val_one,div_one] at h
  rw [h]
  constructor
  · rintro ⟨t,ht⟩
    apply normalizedExteriorIdealRowClass_injective S hS N
    have hc : normalizedExteriorIdealRowClass S hS N i=1 :=
      (QuotientGroup.eq_one_iff _).mpr ⟨t,ht.symm⟩
    rw [hc,normalizedExteriorIdealRowClass,normalizedExteriorIdealRowUnit_principal,map_one]
  · rintro rfl
    exact ⟨1,by rw [normalizedExteriorIdealRowUnit_principal,one_pow]⟩

theorem normalizedExteriorIdealRow_other_not_sixthPower (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : exteriorPrincipalizingPrimes K ⊆ S) (N : ℕ) (hN : 1 ≤ N) (i : ExteriorIdealRowIndex S N)
    (hi : i ≠ normalizedPrincipalRowIndex S hS N hN) :
    ¬∃ t : K, t^6=(normalizedExteriorIdealRowUnit S hS N i : K) :=
  fun h => hi ((normalizedExteriorIdealRow_sixthPower_iff S hS N hN i).mp h)

def normalizedExteriorIdealRowUnits (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : exteriorPrincipalizingPrimes K ⊆ S) (N : ℕ) : Finset Kˣ :=
  Finset.univ.image (normalizedExteriorIdealRowUnit S hS N)

theorem normalizedExteriorIdealRowUnits_card (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : exteriorPrincipalizingPrimes K ⊆ S) (N : ℕ) :
    (normalizedExteriorIdealRowUnits S hS N).card =
      (exteriorBoundedIdealRows S N).card*(exteriorUnitSixthRepresentatives S).card := by
  rw [normalizedExteriorIdealRowUnits,Finset.card_image_of_injective _
    (normalizedExteriorIdealRowUnit_injective S hS N),Finset.card_univ,exteriorIdealRowIndex_card]

end
end ArtinMatthews
