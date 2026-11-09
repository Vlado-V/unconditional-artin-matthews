module

public import ArtinMatthews.SixthExteriorIdealRowClasses


set_option backward.privateInPublic true
@[expose] public section

/-! The literal nonprincipal subset of the finite ideal/S-unit rows.
Exactly one row represents the principal sixth-power class when N>=1. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain
open scoped NumberField nonZeroDivisors Classical
noncomputable section

variable {K : Type} [Field K] [NumberField K]

def IsPrincipalIdealRow (S : Finset (HeightOneSpectrum (𝓞 K))) (N : ℕ)
    (i : ExteriorIdealRowIndex S N) : Prop :=
  ∃ t : K, t^6=(exteriorBoundedIdealRowUnit S N i:K)

theorem isPrincipalIdealRow_iff_class_one
    (S : Finset (HeightOneSpectrum (𝓞 K))) (N : ℕ) (i : ExteriorIdealRowIndex S N) :
    IsPrincipalIdealRow S N i ↔ exteriorBoundedIdealRowClass S N i=1 := by
  have h := field_sixthPower_ratio_iff_unit (exteriorBoundedIdealRowUnit S N i) (1 : Kˣ)
  simp only [Units.val_one,div_one] at h
  rw [IsPrincipalIdealRow,h,exteriorBoundedIdealRowClass]
  constructor
  · rintro ⟨t,ht⟩
    exact (QuotientGroup.eq_one_iff _).mpr ⟨t,ht.symm⟩
  · intro hq
    obtain ⟨t,ht⟩ := (QuotientGroup.eq_one_iff _).mp hq
    exact ⟨t,ht.symm⟩

def nonprincipalIdealRows (S : Finset (HeightOneSpectrum (𝓞 K))) (N : ℕ) :
    Finset (ExteriorIdealRowIndex S N) := Finset.univ.filter (fun i => ¬IsPrincipalIdealRow S N i)

abbrev NonprincipalIdealRowIndex (S : Finset (HeightOneSpectrum (𝓞 K))) (N : ℕ) :=
  {i // i ∈ nonprincipalIdealRows S N}

theorem nonprincipalIdealRow_not_sixthPower
    (S : Finset (HeightOneSpectrum (𝓞 K))) (N : ℕ) (i : NonprincipalIdealRowIndex S N) :
    ¬∃ t : K, t^6=(exteriorBoundedIdealRowUnit S N i.1:K) :=
  (Finset.mem_filter.mp i.2).2

theorem exists_principalIdealRow (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : exteriorPrincipalizingPrimes K ⊆ S) (N : ℕ) (hN : 1 ≤ N) :
    ∃ i : ExteriorIdealRowIndex S N, IsPrincipalIdealRow S N i := by
  have h1 : (1 : Ideal (𝓞 K)) ∈ exteriorBoundedIdealRows S N := by
    apply (mem_exteriorBoundedIdealRows S N 1).mpr
    refine ⟨by simpa using hN,one_ne_zero,?_,?_⟩
    · intro p _
      simpa only [Ideal.one_eq_top,FractionalIdeal.coeIdeal_top] using FractionalIdeal.count_one K p
    · intro p
      rw [Ideal.one_eq_top,FractionalIdeal.coeIdeal_top,FractionalIdeal.count_one]
      norm_num
  let g : Kˣ := exteriorIdealGenerator 1 ((mem_exteriorBoundedIdealRows S N 1).mp h1).2.1
  have hgS : g ∈ exteriorUnitSubgroup S := by
    intro p hp
    rw [exteriorIdealGenerator_valuation _ _ p (fun h => hp (hS h))]
    simpa only [Ideal.one_eq_top,FractionalIdeal.coeIdeal_top] using FractionalIdeal.count_one K p
  let gS : exteriorUnitSubgroup S := ⟨g,hgS⟩
  obtain ⟨r,hr,t,ht⟩ := exteriorUnitSixthRepresentatives_complete S gS⁻¹
  let i : ExteriorIdealRowIndex S N := (⟨1,h1⟩,⟨r,hr⟩)
  refine ⟨i,(isPrincipalIdealRow_iff_class_one S N i).mpr ?_⟩
  let q := QuotientGroup.mk' (globalSixthPowerSubgroup (K := K))
  have hF : g⁻¹=(r:Kˣ)*(t:Kˣ)^6 := congrArg Subtype.val ht
  have he := congrArg q hF
  have hk : q ((t:Kˣ)^6)=1 := (QuotientGroup.eq_one_iff _).mpr ⟨(t:Kˣ),rfl⟩
  rw [map_inv,map_mul,hk] at he
  have he' : (q g)⁻¹=q (r:Kˣ) := he.trans (_root_.mul_one (q (r:Kˣ)))
  change q (g*(r:Kˣ))=1
  rw [map_mul,← he']
  exact mul_inv_cancel (q g)

theorem principalIdealRow_unique (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : exteriorPrincipalizingPrimes K ⊆ S) (N : ℕ)
    {i j : ExteriorIdealRowIndex S N} (hi : IsPrincipalIdealRow S N i)
    (hj : IsPrincipalIdealRow S N j) : i=j :=
  exteriorBoundedIdealRowClass_injective S hS N
    (((isPrincipalIdealRow_iff_class_one S N i).mp hi).trans
      ((isPrincipalIdealRow_iff_class_one S N j).mp hj).symm)

theorem nonprincipalIdealRows_card (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : exteriorPrincipalizingPrimes K ⊆ S) (N : ℕ) (hN : 1 ≤ N) :
    (nonprincipalIdealRows S N).card=
      (exteriorBoundedIdealRows S N).card*(exteriorUnitSixthRepresentatives S).card-1 := by
  have hp : (Finset.univ.filter (IsPrincipalIdealRow S N)).card=1 := by
    apply Finset.card_eq_one_iff_existsUnique.mpr
    obtain ⟨i,hi⟩ := exists_principalIdealRow S hS N hN
    refine ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩,?_⟩
    intro j hj
    exact principalIdealRow_unique S hS N (Finset.mem_filter.mp hj).2 hi
  have he := Finset.card_filter_add_card_filter_not (IsPrincipalIdealRow S N)
    (s := (Finset.univ : Finset (ExteriorIdealRowIndex S N)))
  rw [hp,Finset.card_univ,exteriorIdealRowIndex_card] at he
  change (Finset.univ.filter (fun i => ¬IsPrincipalIdealRow S N i)).card=_
  omega

end
end ArtinMatthews
