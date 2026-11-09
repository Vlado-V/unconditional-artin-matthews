module

public import ArtinMatthews.CubicThetaUnitLift
public import ArtinMatthews.CubicThetaNormCancellation


set_option backward.privateInPublic true
@[expose] public section

/-!
# A norm-one unit above a nontrivial cubic residue character

Surjectivity on units transfers nontriviality from the target residue ring.
The anticyclotomic cubic-character argument then supplies a unit of norm one
in the source on which the pulled-back character remains nontrivial.
-/

namespace ArtinMatthews

/-- A nontrivial unit character stays nontrivial after a surjective finite-ring map. -/
theorem finite_ring_pullback_unit_character_ne_one
    {R S : Type*} [CommRing R] [CommRing S] [Finite R]
    (f : R →+* S) (hf : Function.Surjective f) (χ : S →* ℂ)
    (hne : χ.comp (Units.coeHom S) ≠ 1) :
    (χ.comp f.toMonoidHom).comp (Units.coeHom R) ≠ 1 := by
  intro heq
  apply hne
  ext v
  obtain ⟨u, hu⟩ := units_map_surjective_of_finite f hf v
  have huval : f (u : R) = (v : S) := congrArg (fun w : Sˣ => (w : S)) hu
  have hvalue := congrArg (fun ψ : Rˣ →* ℂ => ψ u) heq
  change χ (f (u : R)) = 1 at hvalue
  rw [huval] at hvalue
  exact hvalue

/-- The source has a norm-one unit detected by the nontrivial cubic target
character. No multiplicative-character extension to nonunits is needed. -/
theorem finite_ring_norm_one_unit_nontrivial
    {R S : Type*} [CommRing R] [CommRing S] [Finite R]
    (f : R →+* S) (hf : Function.Surjective f)
    (κR : R ≃+* R) (κS : S ≃+* S) (hκR : Function.Involutive κR)
    (hcompat : ∀ x : R, f (κR x) = κS (f x))
    (χ : S →* ℂ)
    (hχκ : ∀ v : Sˣ, χ (κS (v : S)) = (χ (v : S))⁻¹)
    (hcubic : ∀ v : Sˣ, χ (v : S) ^ 3 = 1)
    (hne : χ.comp (Units.coeHom S) ≠ 1) :
    ∃ u : Rˣ, (u : R) * κR (u : R) = 1 ∧ χ (f (u : R)) ≠ 1 := by
  let χR : Rˣ →* ℂ := (χ.comp f.toMonoidHom).comp (Units.coeHom R)
  let σR : Rˣ ≃* Rˣ := Units.mapEquiv κR.toMulEquiv
  have hσR : Function.Involutive σR := by
    intro u
    apply Units.ext
    exact hκR (u : R)
  have hχR : χR ≠ 1 := finite_ring_pullback_unit_character_ne_one f hf χ hne
  have hconj (u : Rˣ) : χR (σR u) = (χR u)⁻¹ := by
    change χ (f (κR (u : R))) = (χ (f (u : R)))⁻¹
    rw [hcompat]
    exact hχκ (Units.map f.toMonoidHom u)
  have hcube (u : Rˣ) : χR u ^ 3 = 1 := hcubic (Units.map f.toMonoidHom u)
  obtain ⟨u, huNorm, huχ⟩ := anticyclotomic_cubic_nontrivial_on_norm_kernel
    χR σR (involutionNorm σR) (involutionNorm_map_involution σR hσR)
    hconj hcube hχR
  refine ⟨u, ?_, huχ⟩
  exact congrArg (fun v : Rˣ => (v : R)) huNorm

end ArtinMatthews
