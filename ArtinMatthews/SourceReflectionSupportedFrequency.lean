module

public import ArtinMatthews.SourceReflectionNumeratorReindex
public import ArtinMatthews.SourceReflectionFieldFrequency
public import ArtinMatthews.SourcePrimeExponentProducts
public import ArtinMatthews.SourceFrequencyPoissonArgument


set_option backward.privateInPublic true
@[expose] public section

/-! Combine the fixed denominator with the supported numerator split.
The sixth-power unit in the resulting indexing is the original
norm-one subgroup element. -/
namespace ArtinMatthews.SourceEulerAssembly

open NumberField IsDedekindDomain AllowedGenerators SourcePhysical
open scoped NumberField
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)

local notation "S" => sourceHilbertSet F S₀
local notation "E" => SourcePrimeExponents F S₀
local notation "P₀" => SourceExteriorPrime F S₀
local notation "X" => ExteriorUnitSixthClasses S
local notation "Γ" => sNormOneSixthSubgroup F S
local notation "a" => sourcePrimeExponentUnit F hζ S₀

def sourceReflectionNumeratorExponents (b : Fˣ) (ν : SourceReflectionFieldFrequency F S₀ b) : E :=
  sourceElementExponents F S₀ (sourceReflectionIntegralNumerator F S₀ b ν).val
    (sourceReflectionIntegralNumerator F S₀ b ν).property

theorem sourceReflectionNormOneFrequencyEquiv_exponents (b : Fˣ) (e : E) (u : X) (γ : Γ) :
    sourceReflectionNumeratorExponents F S₀ b
      (sourceReflectionNormOneFrequencyEquiv F S₀ hζ b (e,u,γ)) = e := by
  unfold sourceReflectionNumeratorExponents
  have h := sourceReflectionFieldFrequencyEquiv_numerator F S₀ hζ b e u
    ((sourceExteriorSixthNormOneEquiv F S).symm γ)
  exact (congrArg (fun n : SourceNonzeroFrequency F S₀ =>
    sourceElementExponents F S₀ n.val n.property) h).trans
    (sourceFrequencyMonomial_exponents F hζ S₀ e _)

abbrev SourceReflectionSupportedFrequency (b : Fˣ) (d : E) :=
  {ν : SourceReflectionFieldFrequency F S₀ b //
    (∀ P, sourceReflectionNumeratorExponents F S₀ b ν P % 3 ≤ 1) ∧
    ∀ P ∈ d.support, sourceReflectionNumeratorExponents F S₀ b ν P = 0}

def sourceReflectionSupportedFrequencyEquiv (b : Fˣ) (f : Finset P₀) (d : E) :
    SourceReflectionSupportedTermIndex F S₀ f d × (X × Γ) ≃
      SourceReflectionSupportedFrequency F S₀ b d := by
  let lift : SourceReflectionNumerator F S₀ d × (X × Γ) ≃
      {p : E × (X × Γ) // (∀ P, p.1 P % 3 ≤ 1) ∧ ∀ P ∈ d.support, p.1 P = 0} :=
    { toFun := fun x => ⟨(x.1.val,x.2),x.1.property⟩
      invFun := fun x => (⟨x.val.1,x.property⟩,x.val.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  refine ((sourceReflectionNumeratorEquiv F S₀ f d).symm.prodCongr (Equiv.refl _)).trans
    (lift.trans ((sourceReflectionNormOneFrequencyEquiv F S₀ hζ b).subtypeEquiv ?_))
  rintro ⟨e,u,γ⟩
  rw [sourceReflectionNormOneFrequencyEquiv_exponents]

theorem sourceReflectionSupportedFrequencyEquiv_diagonal (b : Fˣ) (f : Finset P₀) (d : E)
    (i : SourceReflectionSupportedTermIndex F S₀ f d) (u : X) (γ : Γ) :
    sWholeDiagonal F S (sourceReflectionSupportedFrequencyEquiv F S₀ hζ b f d (i,u,γ)).val.val =
      γ.val.val * sWholeDiagonal F S ((sourceExteriorUnitSixthRepresentative S u).val *
        a i.val.1.val * a i.val.2.2.val * (a i.val.2.1)^3 / b^2) := by
  let e := (sourceReflectionCombineNumerator F S₀ f d i).val
  change sWholeDiagonal F S (sourceReflectionNormOneFrequencyEquiv F S₀ hζ b (e,u,γ)).val = _
  rw [sourceReflectionNormOneFrequencyEquiv_diagonal]
  have he : e = i.val.1.val + i.val.2.2.val + 3 • i.val.2.1 := rfl
  have hn : 3 • i.val.2.1 = i.val.2.1 + i.val.2.1 + i.val.2.1 := by
    ext P
    simp only [Finsupp.nsmul_apply, nsmul_eq_mul, Finsupp.add_apply]
    omega
  rw [he, sourcePrimeExponentUnit_add, sourcePrimeExponentUnit_add, hn,
    sourcePrimeExponentUnit_add, sourcePrimeExponentUnit_add, pow_three]
  simp only [mul_assoc]

theorem sourceReflectionSupportedFrequencyEquiv_norm (f : Finset P₀) (d : E)
    (i : SourceReflectionSupportedTermIndex F S₀ f d) (u : X) (γ : Γ) :
    sLocalNorm F S (sWholeDiagonal F S
      (sourceReflectionSupportedFrequencyEquiv F S₀ hζ
        (a (sourceReflectionActiveExponents F S₀ f+d)) f d (i,u,γ)).val.val) =
    sourceReflectionTermLength F S₀ i.val.1.val i.val.2.1 i.val.2.2.val /
      ((sourcePrimeExponentNorm F S₀ d : ℝ)^2 *
        (sourcePrimeExponentNorm F S₀ (sourceReflectionActiveExponents F S₀ f) : ℝ)^2) := by
  rw [sourceReflectionSupportedFrequencyEquiv_diagonal, sLocalNorm_mul]
  have hγ : sLocalNorm F S γ.val.val = 1 := γ.val.property
  rw [hγ, one_mul]
  change fieldSNorm F S _ = _
  have hu : fieldSNorm F S (sourceExteriorUnitSixthRepresentative S u).val = 1 :=
    fieldSNorm_sUnit F S (sourceExteriorUnitToActualSUnit F S
      (sourceExteriorUnitSixthRepresentative S u))
  simp only [map_div, map_mul, map_pow, hu, one_mul, sourcePrimeExponentUnit_fieldSNorm,
    sourcePrimeExponentNorm_add, Nat.cast_mul, mul_pow, sourceReflectionTermLength]
  rw [mul_comm ((sourcePrimeExponentNorm F S₀ (sourceReflectionActiveExponents F S₀ f) : ℝ)^2)]

theorem sourceReflectionSupportedFrequencyEquiv_profile_arg (f : Finset P₀) (d : E)
    (i : SourceReflectionSupportedTermIndex F S₀ f d) (u : X) (γ : Γ) {Z : ℝ} (hZ : 0 < Z) :
    sLocalNorm F S (sWholeDiagonal F S
      (sourceReflectionSupportedFrequencyEquiv F S₀ hζ
        (a (sourceReflectionActiveExponents F S₀ f+d)) f d (i,u,γ)).val.val) / Z⁻¹ =
    sourceReflectionTermLength F S₀ i.val.1.val i.val.2.1 i.val.2.2.val /
      sourceReflectionTermScale F S₀ Z f d := by
  rw [sourceReflectionSupportedFrequencyEquiv_norm, sourceReflectionTermScale]
  have hD : (0 : ℝ) < sourcePrimeExponentNorm F S₀ d :=
    zero_lt_one.trans_le (sourceReflection_norm_one_le F S₀ d)
  have hF : (0 : ℝ) < sourcePrimeExponentNorm F S₀ (sourceReflectionActiveExponents F S₀ f) :=
    zero_lt_one.trans_le (sourceReflection_norm_one_le F S₀ _)
  field_simp [hZ.ne', hD.ne', hF.ne']

end
end ArtinMatthews.SourceEulerAssembly
