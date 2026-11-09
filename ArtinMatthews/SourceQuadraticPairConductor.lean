module

public import ArtinMatthews.SourceQuadraticGcdStrip
public import ArtinMatthews.SourceQuadraticRayProduct
public import ArtinMatthews.SourceQuadraticEuler


set_option backward.privateInPublic true
@[expose] public section

/-! The conductor of the actual residual character in a common-ideal block. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain
open scoped NumberField Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "E" => SourcePrimeExponents F S₀
local notation "I" => sourcePrimeExponentIdeal F S₀
local notation "q" => sourcePrimeExponentNorm F S₀

theorem sourceQuadraticPair_residual_data (b c g : E)
    (hb : sourceReflectionIsSquarefree b) (hc : sourceReflectionIsSquarefree c)
    (hg : b ⊓ c = g) :
    sourceReflectionIsSquarefree (b - g) ∧ sourceReflectionIsSquarefree (c - g) ∧
      Disjoint (b - g).support (c - g).support ∧
      sourceReflectionIsSquarefree ((b - g) + (c - g)) := by
  have hb' := sourceQuadraticExteriorQuotient_squarefree F S₀ b g hb
  have hc' := sourceQuadraticExteriorQuotient_squarefree F S₀ c g hc
  have hd := ((sourceQuadratic_inf_eq_iff_quotient_disjoint F S₀ b c g).mp hg).2.2
  exact ⟨hb', hc', hd, sourceQuadraticDisjoint_add_squarefree F S₀ _ _ hb' hc' hd⟩

theorem sourceQuadraticPair_residual_localClass (b c g : E) (hg : b ⊓ c = g)
    (hclass : sourceQuadraticLocalClass F S₀ hζ b = sourceQuadraticLocalClass F S₀ hζ c) :
    sourceQuadraticLocalClass F S₀ hζ (b - g) =
      sourceQuadraticLocalClass F S₀ hζ (c - g) := by
  obtain ⟨hgb, hgc, _⟩ := (sourceQuadratic_inf_eq_iff_quotient_disjoint F S₀ b c g).mp hg
  have hb : g + (b - g) = b := add_tsub_cancel_of_le hgb
  have hc : g + (c - g) = c := add_tsub_cancel_of_le hgc
  rw [← hb, ← hc, sourceQuadraticLocalClass_add, sourceQuadraticLocalClass_add] at hclass
  exact mul_left_cancel hclass

theorem sourceQuadraticPair_residual_localClass_of_rayClass (b c g : E) (hg : b ⊓ c = g)
    (hclass : sourcePrimeExponentRayClass F S₀ b = sourcePrimeExponentRayClass F S₀ c) :
    sourceQuadraticLocalClass F S₀ hζ (b - g) =
      sourceQuadraticLocalClass F S₀ hζ (c - g) := by
  exact sourceQuadraticPair_residual_localClass F S₀ hζ b c g hg
    (sourcePrimeExponentRayClass_eq_localClass F S₀ hζ b c hclass)

theorem sourceQuadraticPairConductor_eq_product (b c g : E)
    (hb : sourceReflectionIsSquarefree b) (hc : sourceReflectionIsSquarefree c)
    (hg : b ⊓ c = g)
    (hclass : sourceQuadraticLocalClass F S₀ hζ b = sourceQuadraticLocalClass F S₀ hζ c) :
    sourceQuadraticConductor F S₀ hζ ((b - g) + (c - g)) = I (b - g) * I (c - g) := by
  obtain ⟨hb', hc', hd, _⟩ := sourceQuadraticPair_residual_data F S₀ b c g hb hc hg
  exact sourceQuadraticConductor_eq_product_of_class_eq F S₀ hζ _ _ hb' hc' hd
    (sourceQuadraticPair_residual_localClass F S₀ hζ b c g hg hclass)

theorem sourceQuadraticPairConductor_eq_product_of_rayClass (b c g : E)
    (hb : sourceReflectionIsSquarefree b) (hc : sourceReflectionIsSquarefree c)
    (hg : b ⊓ c = g)
    (hclass : sourcePrimeExponentRayClass F S₀ b = sourcePrimeExponentRayClass F S₀ c) :
    sourceQuadraticConductor F S₀ hζ ((b - g) + (c - g)) = I (b - g) * I (c - g) := by
  exact sourceQuadraticPairConductor_eq_product F S₀ hζ b c g hb hc hg
    (sourcePrimeExponentRayClass_eq_localClass F S₀ hζ b c hclass)

theorem sourceQuadraticPairConductor_norm (b c g : E)
    (hb : sourceReflectionIsSquarefree b) (hc : sourceReflectionIsSquarefree c)
    (hg : b ⊓ c = g)
    (hclass : sourceQuadraticLocalClass F S₀ hζ b = sourceQuadraticLocalClass F S₀ hζ c) :
    (sourceQuadraticConductor F S₀ hζ ((b - g) + (c - g))).absNorm =
      q (b - g) * q (c - g) := by
  rw [sourceQuadraticPairConductor_eq_product F S₀ hζ b c g hb hc hg hclass,
    map_mul, sourcePrimeExponentIdeal_norm, sourcePrimeExponentIdeal_norm]

theorem sourceQuadraticPair_residual_eq_zero_iff (b c g : E) (hg : b ⊓ c = g) :
    (b - g) + (c - g) = 0 ↔ b = c := by
  constructor
  · intro h
    obtain ⟨hgb, hgc, _⟩ := (sourceQuadratic_inf_eq_iff_quotient_disjoint F S₀ b c g).mp hg
    ext P
    have hP := congrArg (fun e : E => e P) h
    simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.zero_apply] at hP
    have hbP := hgb P
    have hcP := hgc P
    omega
  · rintro rfl
    have hbg : b = g := by simpa using hg
    subst g
    simp

theorem sourceQuadraticPairConductor_diagonal (b c g : E) (hg : b ⊓ c = g)
    (hbc : b = c) :
    sourceQuadraticConductor F S₀ hζ ((b - g) + (c - g)) = 1 := by
  rw [(sourceQuadraticPair_residual_eq_zero_iff F S₀ b c g hg).mpr hbc,
    sourceQuadraticConductor_zero]

end
end ArtinMatthews.SourceEulerAssembly
