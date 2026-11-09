module

public import ArtinMatthews.SixthExteriorReduction
public import ArtinMatthews.SixthExteriorPowerClassesFinite


set_option backward.privateInPublic true
@[expose] public section

/-! Finite, actual sixth-power representatives of every exterior
valuation fiber. The representatives are obtained from the proved finite
S-unit quotient; no fiber-size or finite-generation premise is supplied. -/
namespace ArtinMatthews
open IsDedekindDomain
open scoped NumberField Classical
noncomputable section

variable {K : Type*} [Field K] [NumberField K]

def exteriorFiberSixthRepresentatives
    (S : Finset (HeightOneSpectrum (𝓞 K))) (u : Kˣ) : Finset Kˣ :=
  (exteriorUnitSixthFieldRepresentatives S).image (fun r : Kˣ => u*r)

theorem exteriorFiberSixthRepresentatives_valuations
    (S : Finset (HeightOneSpectrum (𝓞 K))) (u : Kˣ) {r : Kˣ}
    (hr : r ∈ exteriorFiberSixthRepresentatives S u) :
    ∀ p, p ∉ S → exteriorPrincipalValuation p r=exteriorPrincipalValuation p u := by
  obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hr
  have hwS := exteriorUnitSixthFieldRepresentatives_mem S hw
  intro p hp
  rw [exteriorPrincipalValuation_mul,hwS p hp,add_zero]

theorem exteriorFiberSixthRepresentatives_reduced
    (S : Finset (HeightOneSpectrum (𝓞 K))) (u : Kˣ) (hu : ExteriorSixthReduced S u)
    {r : Kˣ} (hr : r ∈ exteriorFiberSixthRepresentatives S u) : ExteriorSixthReduced S r := by
  intro p hp
  rw [exteriorFiberSixthRepresentatives_valuations S u hr p hp]
  exact hu p hp

/-- Every member of an actual exterior valuation fiber is one of the
constructed finite representatives times an exterior S-unit sixth power. -/
theorem exteriorFiberSixthRepresentatives_complete
    (S : Finset (HeightOneSpectrum (𝓞 K))) (u v : Kˣ)
    (hval : ∀ p, p ∉ S → exteriorPrincipalValuation p v=exteriorPrincipalValuation p u) :
    ∃ r ∈ exteriorFiberSixthRepresentatives S u,
      ∃ t : exteriorUnitSubgroup S, v=r*(t:Kˣ)^6 := by
  have hS : v/u ∈ exteriorUnitSubgroup S := by
    intro p hp
    rw [exteriorPrincipalValuation_div,hval p hp,sub_self]
  obtain ⟨w,hw,t,ht⟩ := exteriorUnitSixthFieldRepresentatives_complete S (v/u) hS
  refine ⟨u*w,Finset.mem_image.mpr ⟨w,hw,rfl⟩,t,?_⟩
  calc
    v = u*(v/u) := by simp [div_eq_mul_inv]
    _ = u*(w*(t:Kˣ)^6) := congrArg (fun z => u*z) ht
    _ = (u*w)*(t:Kˣ)^6 := (mul_assoc _ _ _).symm

theorem exteriorFiberSixthRepresentatives_card_le
    (S : Finset (HeightOneSpectrum (𝓞 K))) (u : Kˣ) :
    (exteriorFiberSixthRepresentatives S u).card ≤
      (exteriorUnitSixthFieldRepresentatives S).card := Finset.card_image_le

end
end ArtinMatthews
