module

public import ArtinMatthews.SourceQuadraticPairScale


set_option backward.privateInPublic true
@[expose] public section

/-! Original class-sliced common pairs inherit the exact residual conductor. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain
open scoped NumberField Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "E" => SourcePrimeExponents F S₀
local notation "I" => sourcePrimeExponentIdeal F S₀

theorem sourceQuadraticClassPair_mem {G : Type*} [DecidableEq G]
    (cols : Finset E) (label : E → G) (κ : G) (p : E × E) (g : E)
    (hp : p ∈ ((sourceQuadraticClassColumns F S₀ cols label κ) ×ˢ
        (sourceQuadraticClassColumns F S₀ cols label κ)).filter
      (fun p : E × E => p.1 ⊓ p.2 = g)) :
    p.1 ∈ cols ∧ p.2 ∈ cols ∧ p.1 ⊓ p.2 = g ∧ label p.1 = label p.2 := by
  obtain ⟨hpair, hg⟩ := Finset.mem_filter.mp hp
  obtain ⟨hb, hc⟩ := Finset.mem_product.mp hpair
  obtain ⟨hb, hbκ⟩ := Finset.mem_filter.mp hb
  obtain ⟨hc, hcκ⟩ := Finset.mem_filter.mp hc
  exact ⟨hb, hc, hg, hbκ.trans hcκ.symm⟩

theorem sourceQuadraticClassPair_local_conductor
    (cols : Finset E) (hcols : ∀ b ∈ cols, sourceReflectionIsSquarefree b)
    (κ : SLocalPowerClasses F 2 (sourceHilbertSet F S₀)) (p : E × E) (g : E)
    (hp : p ∈ ((sourceQuadraticClassColumns F S₀ cols
        (sourceQuadraticLocalClass F S₀ hζ) κ) ×ˢ
        (sourceQuadraticClassColumns F S₀ cols (sourceQuadraticLocalClass F S₀ hζ) κ)).filter
      (fun p : E × E => p.1 ⊓ p.2 = g)) :
    sourceReflectionIsSquarefree ((p.1 - g) + (p.2 - g)) ∧
      sourceQuadraticLocalClass F S₀ hζ (p.1 - g) =
        sourceQuadraticLocalClass F S₀ hζ (p.2 - g) ∧
      sourceQuadraticConductor F S₀ hζ ((p.1 - g) + (p.2 - g)) =
        I (p.1 - g) * I (p.2 - g) := by
  obtain ⟨hb, hc, hg, hclass⟩ := sourceQuadraticClassPair_mem F S₀ cols _ κ p g hp
  exact ⟨(sourceQuadraticPair_residual_data F S₀ _ _ _ (hcols _ hb) (hcols _ hc) hg).2.2.2,
    sourceQuadraticPair_residual_localClass F S₀ hζ _ _ _ hg hclass,
    sourceQuadraticPairConductor_eq_product F S₀ hζ _ _ _ (hcols _ hb) (hcols _ hc) hg hclass⟩

theorem sourceQuadraticClassPair_ray_conductor
    (cols : Finset E) (hcols : ∀ b ∈ cols, sourceReflectionIsSquarefree b)
    (κ : SourceQuadraticRayClass F S₀) (p : E × E) (g : E)
    (hp : p ∈ ((sourceQuadraticClassColumns F S₀ cols
        (sourcePrimeExponentRayClass F S₀) κ) ×ˢ
        (sourceQuadraticClassColumns F S₀ cols (sourcePrimeExponentRayClass F S₀) κ)).filter
      (fun p : E × E => p.1 ⊓ p.2 = g)) :
    sourceReflectionIsSquarefree ((p.1 - g) + (p.2 - g)) ∧
      sourceQuadraticLocalClass F S₀ hζ (p.1 - g) =
        sourceQuadraticLocalClass F S₀ hζ (p.2 - g) ∧
      sourceQuadraticConductor F S₀ hζ ((p.1 - g) + (p.2 - g)) =
        I (p.1 - g) * I (p.2 - g) := by
  obtain ⟨hb, hc, hg, hclass⟩ := sourceQuadraticClassPair_mem F S₀ cols _ κ p g hp
  have hlocal := sourcePrimeExponentRayClass_eq_localClass F S₀ hζ p.1 p.2 hclass
  exact ⟨(sourceQuadraticPair_residual_data F S₀ _ _ _ (hcols _ hb) (hcols _ hc) hg).2.2.2,
    sourceQuadraticPair_residual_localClass F S₀ hζ _ _ _ hg hlocal,
    sourceQuadraticPairConductor_eq_product F S₀ hζ _ _ _ (hcols _ hb) (hcols _ hc) hg hlocal⟩

end
end ArtinMatthews.SourceEulerAssembly
