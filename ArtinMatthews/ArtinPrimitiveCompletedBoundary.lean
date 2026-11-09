module

public import ArtinMatthews.ArtinPrimitiveConductorOneBoundary
public import ArtinMatthews.VaryingKummerAnalyticPrimitiveCompletionIdentity


set_option backward.privateInPublic true
@[expose] public section

/-! The proper-conductor branch of actual Frobenius primitive boundary
nonvanishing. All family, nonprincipal and conductor-descent hypotheses are
retained; no boundary theorem for arbitrary ideal characters is assumed. -/
namespace ArtinMatthews.AbelianLocal
open ArtinMatthews.VaryingKummerAnalytic NumberField RayClass
open OAI.SevenEighths.FiniteFourier
open scoped NumberField IsMulCommutative Classical ComplexConjugate
noncomputable section
variable (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E]
variable [Algebra F E] [IsAbelianGalois F E]
variable {N : ℕ} [NeZero N]
variable (ψ : (Gal(E/F) →* ℂˣ) → EvenRayCharacter F N)
variable (hψ : ∀ χ, (ψ χ).idealHom = GaloisIdealCharacter.idealHom F E χ)
variable (hD : (NumberField.discr E).natAbs ∣ N)
variable (hnp : ∀ χ, χ ≠ 1 → (ψ χ).IsNonprincipal)
variable (χ : Gal(E/F) →* ℂˣ) (hχ : χ ≠ 1)
variable (f : Ideal (𝓞 F)) (hf : f ≠ ⊥)
variable (hMf : rationalModulusIdeal (𝓞 F) N ≤ f) (Ψ : EvenIdealRayCharacter F f)
variable (hprim : IsPrimitiveOnIdeals Ψ.residue)
variable (hagree : ∀ I : primeToModulusIdeals (rationalIdealRayModulus F N),
  Ψ.idealHom (I:FractionalIdealGroup F) = (ψ χ).idealHom (I:FractionalIdealGroup F))
include hψ hD hnp hχ hMf hagree hprim


theorem artinRay_properCompleted_one_ne_zero (hft : f ≠ ⊤) :
    Ψ.properCompleted hf hft 1 ≠ 0 := by
  have hΨ := (ψ χ).primitiveIdeal_isNonprincipal f hMf Ψ hagree (hnp χ hχ)
  exact fun hz => artinRay_primitiveContinued_one_ne_zero F E ψ hψ hD hnp χ hχ
    f hf hMf Ψ hprim hagree
    ((Ψ.properCompleted_zero_iff_primitive hf hft hprim hΨ (s := 1) (by norm_num)).mp hz)

theorem artinRay_inverse_properCompleted_one_ne_zero (hft : f ≠ ⊤) :
    Ψ.inverse.properCompleted hf hft 1 ≠ 0 := by
  have hΨ := (ψ χ).primitiveIdeal_isNonprincipal f hMf Ψ hagree (hnp χ hχ)
  exact fun hz => artinRay_inverse_primitiveContinued_one_ne_zero F E ψ hψ hD hnp χ hχ
    f hf hMf Ψ hprim hagree
    ((Ψ.inverse.properCompleted_zero_iff_primitive hf hft (Ψ.inverse_isPrimitive hf hprim)
      (Ψ.inverse_isNonprincipal hΨ) (s := 1) (by norm_num)).mp hz)

theorem artinRay_properCompleted_zero_ne_zero (hft : f ≠ ⊤) :
    Ψ.properCompleted hf hft 0 ≠ 0 := by
  obtain ⟨W,hW,HW⟩ := Ψ.properCompleted_functionalEquation hf hft hprim
  rw [HW 0,sub_zero]
  apply mul_ne_zero
  · exact fun hz => zero_ne_one (by simpa only [hz,norm_zero] using hW)
  · exact artinRay_inverse_properCompleted_one_ne_zero F E ψ hψ hD hnp χ hχ
      f hf hMf Ψ hprim hagree hft



include hf in
theorem artinRay_inverse_conductorOneCompleted_zero_ne_zero (hft : f = ⊤) :
    Ψ.inverse.conductorOneCompleted hft 0 ≠ 0 := by
  have hΨ := (ψ χ).primitiveIdeal_isNonprincipal f hMf Ψ hagree (hnp χ hχ)
  intro hz
  have H := Ψ.conductorOneCompleted_functional_equation hft hΨ 1
  simp only [sub_self,hz,mul_zero] at H
  exact artinRay_conductorOneCompleted_one_ne_zero F E ψ hψ hD hnp χ hχ
    f hf hMf Ψ hprim hagree hft H


theorem artinRay_inverse_properCompleted_zero_ne_zero (hft : f ≠ ⊤) :
    Ψ.inverse.properCompleted hf hft 0 ≠ 0 := by
  intro hz
  obtain ⟨W,_hW,HW⟩ := Ψ.properCompleted_functionalEquation hf hft hprim
  have H := HW 1
  simp only [sub_self,hz,mul_zero] at H
  exact artinRay_properCompleted_one_ne_zero F E ψ hψ hD hnp χ hχ
    f hf hMf Ψ hprim hagree hft H

omit hMf hagree hprim in
/-- A genuine primitive descendant with nonzero endpoints exists in either
conductor branch, retaining the original Frobenius ideal values. -/
theorem artinRay_exists_primitive_completed_boundary_nonzero :
    ∃ (f : Ideal (𝓞 F)) (hf : f ≠ ⊥)
      (_hMf : rationalModulusIdeal (𝓞 F) N ≤ f) (Ψ : EvenIdealRayCharacter F f)
      (hprim : IsPrimitiveOnIdeals Ψ.residue),
      Ψ.IsNonprincipal ∧ f.absNorm ≤ (rationalModulusIdeal (𝓞 F) N).absNorm ∧
      (∀ I : primeToModulusIdeals (rationalIdealRayModulus F N),
        Ψ.idealHom (I:FractionalIdealGroup F) = (ψ χ).idealHom (I:FractionalIdealGroup F)) ∧
      (∀ hft : f ≠ ⊤, Ψ.properCompleted hf hft 0 ≠ 0 ∧ Ψ.properCompleted hf hft 1 ≠ 0) ∧
      (∀ hft : f = ⊤, Ψ.conductorOneCompleted hft 0 ≠ 0 ∧ Ψ.conductorOneCompleted hft 1 ≠ 0) ∧
      Ψ.primitiveContinued hf hprim 1 ≠ 0 := by
  obtain ⟨f,hf,hMf,Ψ,hprim,hΨ,hnorm,hagree,hL,_hLi⟩ :=
    artinRay_exists_primitive_boundary_nonzero F E ψ hψ hD hnp χ hχ
  refine ⟨f,hf,hMf,Ψ,hprim,hΨ,hnorm,hagree,?_,?_,hL⟩
  · intro hft
    exact ⟨artinRay_properCompleted_zero_ne_zero F E ψ hψ hD hnp χ hχ f hf hMf Ψ hprim hagree hft,
      artinRay_properCompleted_one_ne_zero F E ψ hψ hD hnp χ hχ f hf hMf Ψ hprim hagree hft⟩
  · intro hft
    exact ⟨artinRay_conductorOneCompleted_zero_ne_zero F E ψ hψ hD hnp χ hχ f hf hMf Ψ hprim hagree hft,
      artinRay_conductorOneCompleted_one_ne_zero F E ψ hψ hD hnp χ hχ f hf hMf Ψ hprim hagree hft⟩

omit hMf hagree hprim in
/-- The same actual primitive descendant and its inverse have nonzero
completed values at zero and one, with both original primitive values at one
retained. The arithmetic family and all descent hypotheses remain explicit. -/
theorem artinRay_exists_primitive_completed_pair_boundary_nonzero :
    ∃ (f : Ideal (𝓞 F)) (hf : f ≠ ⊥)
      (_hMf : rationalModulusIdeal (𝓞 F) N ≤ f) (Ψ : EvenIdealRayCharacter F f)
      (hprim : IsPrimitiveOnIdeals Ψ.residue),
      Ψ.IsNonprincipal ∧ f.absNorm ≤ (rationalModulusIdeal (𝓞 F) N).absNorm ∧
      (∀ I : primeToModulusIdeals (rationalIdealRayModulus F N),
        Ψ.idealHom (I:FractionalIdealGroup F) = (ψ χ).idealHom (I:FractionalIdealGroup F)) ∧
      (∀ hft : f ≠ ⊤,
        Ψ.properCompleted hf hft 0 ≠ 0 ∧ Ψ.properCompleted hf hft 1 ≠ 0 ∧
        Ψ.inverse.properCompleted hf hft 0 ≠ 0 ∧ Ψ.inverse.properCompleted hf hft 1 ≠ 0) ∧
      (∀ hft : f = ⊤,
        Ψ.conductorOneCompleted hft 0 ≠ 0 ∧ Ψ.conductorOneCompleted hft 1 ≠ 0 ∧
        Ψ.inverse.conductorOneCompleted hft 0 ≠ 0 ∧
        Ψ.inverse.conductorOneCompleted hft 1 ≠ 0) ∧
      Ψ.primitiveContinued hf hprim 1 ≠ 0 ∧
      Ψ.inverse.primitiveContinued hf (Ψ.inverse_isPrimitive hf hprim) 1 ≠ 0 := by
  obtain ⟨f,hf,hMf,Ψ,hprim,hΨ,hnorm,hagree,hL,hLi⟩ :=
    artinRay_exists_primitive_boundary_nonzero F E ψ hψ hD hnp χ hχ
  refine ⟨f,hf,hMf,Ψ,hprim,hΨ,hnorm,hagree,?_,?_,hL,hLi⟩
  · intro hft
    exact ⟨artinRay_properCompleted_zero_ne_zero F E ψ hψ hD hnp χ hχ f hf hMf Ψ hprim hagree hft,
      artinRay_properCompleted_one_ne_zero F E ψ hψ hD hnp χ hχ f hf hMf Ψ hprim hagree hft,
      artinRay_inverse_properCompleted_zero_ne_zero F E ψ hψ hD hnp χ hχ f hf hMf Ψ hprim hagree hft,
      artinRay_inverse_properCompleted_one_ne_zero F E ψ hψ hD hnp χ hχ f hf hMf Ψ hprim hagree hft⟩
  · intro hft
    exact ⟨artinRay_conductorOneCompleted_zero_ne_zero F E ψ hψ hD hnp χ hχ f hf hMf Ψ hprim hagree hft,
      artinRay_conductorOneCompleted_one_ne_zero F E ψ hψ hD hnp χ hχ f hf hMf Ψ hprim hagree hft,
      artinRay_inverse_conductorOneCompleted_zero_ne_zero F E ψ hψ hD hnp χ hχ f hf hMf Ψ hprim hagree hft,
      artinRay_inverse_conductorOneCompleted_one_ne_zero F E ψ hψ hD hnp χ hχ f hf hMf Ψ hprim hagree hft⟩

end
end ArtinMatthews.AbelianLocal
