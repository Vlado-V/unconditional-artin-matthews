module

public import ArtinMatthews.SLocalSixthComplement


set_option backward.privateInPublic true
@[expose] public section

/-! Actual self-orthogonality of the S-unit image. It is deduced from
the constructed isotropic complement and the genuine nondegenerate
Hilbert pairing, never supplied as a maximality premise. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain
open scoped NumberField Classical
noncomputable section

theorem multiplicative_selfOrthogonal_of_isCompl
    {G T : Type*} [CommGroup G] [CommGroup T] (H : G →* (G →* T))
    (hNondeg : ∀ x, (∀ y, H x y = 1) → x = 1)
    (E B : Subgroup G) (hCompl : IsCompl E B)
    (hE : ∀ x ∈ E, ∀ y ∈ E, H x y = 1)
    (hB : ∀ x ∈ B, ∀ y ∈ B, H x y = 1) :
    ∀ x, (∀ y ∈ E, H x y = 1) ↔ x ∈ E := by
  intro x
  constructor
  · intro hx
    have hTop : E ⊔ B = ⊤ := codisjoint_iff.mp hCompl.codisjoint
    have hxTop : x ∈ E ⊔ B := by rw [hTop]; trivial
    obtain ⟨e, he, b, hb, heb⟩ := Subgroup.mem_sup.mp hxTop
    have hbE : ∀ y ∈ E, H b y = 1 := by
      intro y hy
      have h := hx y hy
      rw [← heb, map_mul, MonoidHom.mul_apply, hE e he y hy, one_mul] at h
      exact h
    have hbAll : ∀ y, H b y = 1 := by
      intro y
      have hyTop : y ∈ E ⊔ B := by rw [hTop]; trivial
      obtain ⟨e', he', b', hb', rfl⟩ := Subgroup.mem_sup.mp hyTop
      rw [map_mul, hbE e' he', hB b hb b' hb', one_mul]
    have hbOne := hNondeg b hbAll
    rw [← heb, hbOne, mul_one]
    exact he
  · intro hx y hy
    exact hE x hx y hy

variable (K : Type) [Field K] [NumberField K]

theorem source_sixth_unitImage_selfOrthogonal {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    ∀ x : SLocalPowerClasses K 6 (sourceHilbertSet K S₀),
      (∀ y ∈ sUnitPowerImage K 6 (sourceHilbertSet K S₀),
        sLocalHilbertForm K 6 (sLocalPrimitiveRoots K 6 (sourceHilbertRootSix_isPrimitive K hζ))
          (sourceHilbertSet K S₀) x y = 1) ↔ x ∈ sUnitPowerImage K 6 (sourceHilbertSet K S₀) := by
  let : NumberField.IsTotallyComplex K := source_isTotallyComplex K hζ
  obtain ⟨B, hC, hI⟩ := source_sixth_isotropic_complement K hζ S₀
  apply multiplicative_selfOrthogonal_of_isCompl _
    (sLocalHilbertForm_nondegenerate_left K 6 _ (sourceHilbertSet K S₀)) _ B hC _ hI
  exact sLocalHilbertForm_unitImage_isotropic K 6 (by norm_num) _ (sourceHilbertSet K S₀)
    (normSupport_exponent_subset K 6 _
      (normSupport_subset_sourceHilbertSet K S₀ 6 (Or.inr (Or.inr rfl))))

end
end ArtinMatthews
