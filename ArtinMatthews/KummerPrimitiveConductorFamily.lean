module

public import ArtinMatthews.KummerPrimitiveRowInjectivity
public import ArtinMatthews.FiniteFamilyFiberCounts


set_option backward.privateInPublic true
@[expose] public section

/-! Regroup the actual chosen primitive rows by their actual ideal
conductors. The coefficient image at each conductor and every filtered
row count are identified exactly, without duplicate presentations. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain VaryingKummerAnalytic
open OAI.SevenEighths.FiniteFourier
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section

variable {K : Type} [Field K] [NumberField K] [Algebra K ℂ]
variable [NumberField.IsTotallyComplex K]

def transportIdealRayCharacter {M f : IdealConductorModulus K} (h : M=f)
    (ψ : EvenIdealRayCharacter K M.val) : EvenIdealRayCharacter K f.val :=
  h ▸ ψ

omit [Algebra K ℂ] [NumberField.IsTotallyComplex K] in
theorem transportIdealRayCharacter_coefficient {M f : IdealConductorModulus K} (h : M=f)
    (ψ : EvenIdealRayCharacter K M.val) :
    (transportIdealRayCharacter h ψ).coefficient=ψ.coefficient := by cases h; rfl

omit [Algebra K ℂ] [NumberField.IsTotallyComplex K] in
theorem transportIdealRayCharacter_primitive {M f : IdealConductorModulus K} (h : M=f)
    (ψ : EvenIdealRayCharacter K M.val) (hψ : IsPrimitiveOnIdeals ψ.residue) :
    IsPrimitiveOnIdeals (transportIdealRayCharacter h ψ).residue := by cases h; exact hψ

omit [Algebra K ℂ] [NumberField.IsTotallyComplex K] in
theorem transportIdealRayCharacter_nonprincipal {M f : IdealConductorModulus K} (h : M=f)
    (ψ : EvenIdealRayCharacter K M.val) (hψ : ψ.IsNonprincipal) :
    (transportIdealRayCharacter h ψ).IsNonprincipal := by cases h; exact hψ

def chosenPrimitiveConductorSupport {ζ : K} (hζ : IsPrimitiveRoot ζ 6)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hWild : sixthWildPrimes K ⊆ S)
    (hClass : exteriorPrincipalizingPrimes K ⊆ S) (N : ℕ) : Finset (IdealConductorModulus K) :=
  Finset.univ.image (fun i => (chosenKummerPrimitiveDatum hζ S hWild hClass N i).modulus)

def chosenPrimitiveIndicesAt {ζ : K} (hζ : IsPrimitiveRoot ζ 6)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hWild : sixthWildPrimes K ⊆ S)
    (hClass : exteriorPrincipalizingPrimes K ⊆ S) (N : ℕ) (M : IdealConductorModulus K) :
    Finset (NonprincipalIdealRowIndex S N) :=
  Finset.univ.filter (fun i => (chosenKummerPrimitiveDatum hζ S hWild hClass N i).modulus=M)

theorem mem_chosenPrimitiveIndicesAt {ζ : K} (hζ : IsPrimitiveRoot ζ 6)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hWild : sixthWildPrimes K ⊆ S)
    (hClass : exteriorPrincipalizingPrimes K ⊆ S) (N : ℕ) (M : IdealConductorModulus K)
    (i : NonprincipalIdealRowIndex S N) :
    i ∈ chosenPrimitiveIndicesAt hζ S hWild hClass N M ↔
      (chosenKummerPrimitiveDatum hζ S hWild hClass N i).modulus=M := by
  simp only [chosenPrimitiveIndicesAt,Finset.mem_filter,Finset.mem_univ,true_and]

def chosenPrimitiveCharactersAt {ζ : K} (hζ : IsPrimitiveRoot ζ 6)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hWild : sixthWildPrimes K ⊆ S)
    (hClass : exteriorPrincipalizingPrimes K ⊆ S) (N : ℕ) (M : IdealConductorModulus K) :
    Finset (EvenIdealRayCharacter K M.val) :=
  (chosenPrimitiveIndicesAt hζ S hWild hClass N M).attach.image
    (fun i : {i // i ∈ chosenPrimitiveIndicesAt hζ S hWild hClass N M} =>
      transportIdealRayCharacter ((mem_chosenPrimitiveIndicesAt hζ S hWild hClass N M i.1).mp i.2)
      (chosenKummerPrimitiveDatum hζ S hWild hClass N i.1).character)

theorem mem_chosenPrimitiveCharactersAt {ζ : K} (hζ : IsPrimitiveRoot ζ 6)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hWild : sixthWildPrimes K ⊆ S)
    (hClass : exteriorPrincipalizingPrimes K ⊆ S) (N : ℕ) (M : IdealConductorModulus K)
    (ψ : EvenIdealRayCharacter K M.val) :
    ψ ∈ chosenPrimitiveCharactersAt hζ S hWild hClass N M ↔
      ∃ (i : NonprincipalIdealRowIndex S N)
        (h : (chosenKummerPrimitiveDatum hζ S hWild hClass N i).modulus=M),
        transportIdealRayCharacter h (chosenKummerPrimitiveDatum hζ S hWild hClass N i).character=ψ := by
  constructor
  · intro hψ
    unfold chosenPrimitiveCharactersAt at hψ
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hψ
    exact ⟨i.1,(mem_chosenPrimitiveIndicesAt hζ S hWild hClass N M i.1).mp i.2,rfl⟩
  · rintro ⟨i,h,rfl⟩
    let j : {i : NonprincipalIdealRowIndex S N // i ∈ chosenPrimitiveIndicesAt hζ S hWild hClass N M} :=
      ⟨i,(mem_chosenPrimitiveIndicesAt hζ S hWild hClass N M i).mpr h⟩
    unfold chosenPrimitiveCharactersAt
    exact Finset.mem_image.mpr ⟨j,Finset.mem_attach _ j,rfl⟩

theorem chosenPrimitiveCharactersAt_primitive {ζ : K} (hζ : IsPrimitiveRoot ζ 6)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hWild : sixthWildPrimes K ⊆ S)
    (hClass : exteriorPrincipalizingPrimes K ⊆ S) (N : ℕ) (M : IdealConductorModulus K)
    (ψ : EvenIdealRayCharacter K M.val) (hψ : ψ ∈ chosenPrimitiveCharactersAt hζ S hWild hClass N M) :
    IsPrimitiveOnIdeals ψ.residue := by
  obtain ⟨i,h,rfl⟩ := (mem_chosenPrimitiveCharactersAt hζ S hWild hClass N M ψ).mp hψ
  exact transportIdealRayCharacter_primitive h _ (chosenKummerPrimitiveDatum hζ S hWild hClass N i).primitive

theorem chosenPrimitiveCharactersAt_nonprincipal {ζ : K} (hζ : IsPrimitiveRoot ζ 6)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hWild : sixthWildPrimes K ⊆ S)
    (hClass : exteriorPrincipalizingPrimes K ⊆ S) (N : ℕ) (M : IdealConductorModulus K)
    (ψ : EvenIdealRayCharacter K M.val) (hψ : ψ ∈ chosenPrimitiveCharactersAt hζ S hWild hClass N M) :
    ψ.IsNonprincipal := by
  obtain ⟨i,h,rfl⟩ := (mem_chosenPrimitiveCharactersAt hζ S hWild hClass N M ψ).mp hψ
  exact transportIdealRayCharacter_nonprincipal h _ (chosenKummerPrimitiveDatum hζ S hWild hClass N i).nonprincipal

theorem chosenPrimitiveCharactersAt_coefficient_image {ζ : K} (hζ : IsPrimitiveRoot ζ 6)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hWild : sixthWildPrimes K ⊆ S)
    (hClass : exteriorPrincipalizingPrimes K ⊆ S) (N : ℕ) (M : IdealConductorModulus K) :
    (chosenPrimitiveCharactersAt hζ S hWild hClass N M).image (fun ψ => ψ.coefficient)=
      finiteFamilyImageAt (fun i => (chosenKummerPrimitiveDatum hζ S hWild hClass N i).modulus)
        (fun i => (chosenKummerPrimitiveDatum hζ S hWild hClass N i).character.coefficient) M := by
  ext c
  constructor
  · intro hc
    obtain ⟨ψ,hψ,rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨i,h,rfl⟩ := (mem_chosenPrimitiveCharactersAt hζ S hWild hClass N M ψ).mp hψ
    exact (mem_finiteFamilyImageAt _ _ M _).mpr ⟨i,h,(transportIdealRayCharacter_coefficient h _).symm⟩
  · intro hc
    obtain ⟨i,h,he⟩ := (mem_finiteFamilyImageAt _ _ M c).mp hc
    refine Finset.mem_image.mpr ⟨transportIdealRayCharacter h
      (chosenKummerPrimitiveDatum hζ S hWild hClass N i).character,?_,?_⟩
    · exact (mem_chosenPrimitiveCharactersAt hζ S hWild hClass N M _).mpr ⟨i,h,rfl⟩
    · exact (transportIdealRayCharacter_coefficient h _).trans he

def primitiveRowConductorBudget (S : Finset (HeightOneSpectrum (𝓞 K))) (N : ℕ) : ℝ :=
  ((sixthKummerFixedIdeal S).absNorm:ℝ)*(N:ℝ)

omit [Algebra K ℂ] [NumberField.IsTotallyComplex K] in
theorem primitiveRowConductorBudget_ge_one (S : Finset (HeightOneSpectrum (𝓞 K)))
    (N : ℕ) (hN : 1 ≤ N) : 1 ≤ primitiveRowConductorBudget S N := by
  have h : 1 ≤ (sixthKummerFixedIdeal S).absNorm*N := Nat.succ_le_of_lt
    (Nat.mul_pos (sixthKummerFixedIdeal_absNorm_pos S) (Nat.lt_of_lt_of_le (by decide : 0 < 1) hN))
  change (1:ℝ) ≤ ((sixthKummerFixedIdeal S).absNorm:ℝ)*(N:ℝ)
  exact_mod_cast h

theorem chosenPrimitiveConductorSupport_norm_le {ζ : K} (hζ : IsPrimitiveRoot ζ 6)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hWild : sixthWildPrimes K ⊆ S)
    (hClass : exteriorPrincipalizingPrimes K ⊆ S) (N : ℕ)
    (M : IdealConductorModulus K) (hM : M ∈ chosenPrimitiveConductorSupport hζ S hWild hClass N) :
    (M.val.absNorm:ℝ) ≤ primitiveRowConductorBudget S N := by
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hM
  change (((chosenKummerPrimitiveDatum hζ S hWild hClass N i).modulus.val).absNorm:ℝ) ≤
    ((sixthKummerFixedIdeal S).absNorm:ℝ)*(N:ℝ)
  exact_mod_cast (chosenKummerPrimitiveDatum hζ S hWild hClass N i).norm_le

theorem chosenPrimitiveCharactersAt_filtered_count_sum {ζ : K} (hζ : IsPrimitiveRoot ζ 6)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hWild : sixthWildPrimes K ⊆ S)
    (hClass : exteriorPrincipalizingPrimes K ⊆ S) (N : ℕ)
    (P : (integralFractionalIdeals K → ℂ) → Prop) :
    (∑ M ∈ chosenPrimitiveConductorSupport hζ S hWild hClass N,
      (((chosenPrimitiveCharactersAt hζ S hWild hClass N M).image (fun ψ => ψ.coefficient)).filter P).card)=
      (Finset.univ.filter (fun i => P (chosenKummerPrimitiveDatum hζ S hWild hClass N i).character.coefficient)).card := by
  calc
    _ = ∑ M ∈ chosenPrimitiveConductorSupport hζ S hWild hClass N,
        ((finiteFamilyImageAt
          (fun i => (chosenKummerPrimitiveDatum hζ S hWild hClass N i).modulus)
          (fun i => (chosenKummerPrimitiveDatum hζ S hWild hClass N i).character.coefficient) M).filter P).card := by
      apply Finset.sum_congr rfl
      intro M _
      rw [chosenPrimitiveCharactersAt_coefficient_image]
    _ = _ := by
      rw [chosenPrimitiveConductorSupport,
        finiteFamilyImageAt_filter_card_sum _ _
          (chosenKummerPrimitiveDatum_coefficient_injective hζ S hWild hClass N),
        Finset.filter_image,Finset.card_image_of_injective _
          (chosenKummerPrimitiveDatum_coefficient_injective hζ S hWild hClass N)]

end
end ArtinMatthews
