module

public import ArtinMatthews.ArtinFrobeniusCompletedBoundary
public import ArtinMatthews.VaryingKummerAnalyticPrimitiveCompletedUnifiedAnalytic


set_option backward.privateInPublic true
@[expose] public section

/-! Boundary nonvanishing of the genuinely normalized unified completion
for actual abelian Frobenius primitive descendants. Every arithmetic family
and conductor-descent hypothesis is retained. -/
namespace ArtinMatthews.AbelianLocal
open ArtinMatthews.VaryingKummerAnalytic NumberField RayClass
open OAI.SevenEighths.FiniteFourier
open scoped NumberField IsMulCommutative Classical
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
include hψ hD hnp hχ hMf hprim hagree

theorem artinRay_primitiveCompletedUnified_one_ne_zero :
    Ψ.primitiveCompletedUnified hf 1 ≠ 0 := by
  have hΨ := (ψ χ).primitiveIdeal_isNonprincipal f hMf Ψ hagree (hnp χ hχ)
  exact fun hz => artinRay_primitiveContinued_one_ne_zero F E ψ hψ hD hnp χ hχ
    f hf hMf Ψ hprim hagree
    ((Ψ.primitiveCompletedUnified_zero_iff_primitive hf hprim hΨ (s := 1) (by norm_num)).mp hz)

theorem artinRay_inverse_primitiveCompletedUnified_one_ne_zero :
    Ψ.inverse.primitiveCompletedUnified hf 1 ≠ 0 := by
  have hΨ := (ψ χ).primitiveIdeal_isNonprincipal f hMf Ψ hagree (hnp χ hχ)
  exact fun hz => artinRay_inverse_primitiveContinued_one_ne_zero F E ψ hψ hD hnp χ hχ
    f hf hMf Ψ hprim hagree
    ((Ψ.inverse.primitiveCompletedUnified_zero_iff_primitive hf
      (Ψ.inverse_isPrimitive hf hprim) (Ψ.inverse_isNonprincipal hΨ)
      (s := 1) (by norm_num)).mp hz)

theorem artinRay_primitiveCompletedUnified_zero_ne_zero :
    Ψ.primitiveCompletedUnified hf 0 ≠ 0 := by
  have hΨ := (ψ χ).primitiveIdeal_isNonprincipal f hMf Ψ hagree (hnp χ hχ)
  obtain ⟨W,hW,HW⟩ := Ψ.primitiveCompletedUnified_functionalEquation hf hprim hΨ
  rw [HW 0,sub_zero]
  apply mul_ne_zero
  · exact fun hz => zero_ne_one (by simpa only [hz,norm_zero] using hW)
  · exact artinRay_inverse_primitiveCompletedUnified_one_ne_zero F E ψ hψ hD hnp χ hχ
      f hf hMf Ψ hprim hagree

theorem artinRay_inverse_primitiveCompletedUnified_zero_ne_zero :
    Ψ.inverse.primitiveCompletedUnified hf 0 ≠ 0 := by
  have hΨ := (ψ χ).primitiveIdeal_isNonprincipal f hMf Ψ hagree (hnp χ hχ)
  intro hz
  obtain ⟨W,_hW,HW⟩ := Ψ.primitiveCompletedUnified_functionalEquation hf hprim hΨ
  have H := HW 1
  simp only [sub_self,hz,mul_zero] at H
  exact artinRay_primitiveCompletedUnified_one_ne_zero F E ψ hψ hD hnp χ hχ
    f hf hMf Ψ hprim hagree H

omit hMf hprim hagree in
theorem artinRay_exists_primitiveCompletedUnified_boundary_nonzero :
    ∃ (f : Ideal (𝓞 F)) (hf : f ≠ ⊥)
      (_hMf : rationalModulusIdeal (𝓞 F) N ≤ f) (Ψ : EvenIdealRayCharacter F f)
      (hprim : IsPrimitiveOnIdeals Ψ.residue),
      Ψ.IsNonprincipal ∧ f.absNorm ≤ (rationalModulusIdeal (𝓞 F) N).absNorm ∧
      (∀ I : primeToModulusIdeals (rationalIdealRayModulus F N),
        Ψ.idealHom (I:FractionalIdealGroup F) = (ψ χ).idealHom (I:FractionalIdealGroup F)) ∧
      Ψ.primitiveCompletedUnified hf 0 ≠ 0 ∧ Ψ.primitiveCompletedUnified hf 1 ≠ 0 ∧
      Ψ.inverse.primitiveCompletedUnified hf 0 ≠ 0 ∧
      Ψ.inverse.primitiveCompletedUnified hf 1 ≠ 0 ∧
      Ψ.primitiveContinued hf hprim 1 ≠ 0 ∧
      Ψ.inverse.primitiveContinued hf (Ψ.inverse_isPrimitive hf hprim) 1 ≠ 0 := by
  obtain ⟨f,hf,hMf,Ψ,hprim,hΨ,hnorm,hagree,hL,hLi⟩ :=
    artinRay_exists_primitive_boundary_nonzero F E ψ hψ hD hnp χ hχ
  exact ⟨f,hf,hMf,Ψ,hprim,hΨ,hnorm,hagree,
    artinRay_primitiveCompletedUnified_zero_ne_zero F E ψ hψ hD hnp χ hχ f hf hMf Ψ hprim hagree,
    artinRay_primitiveCompletedUnified_one_ne_zero F E ψ hψ hD hnp χ hχ f hf hMf Ψ hprim hagree,
    artinRay_inverse_primitiveCompletedUnified_zero_ne_zero F E ψ hψ hD hnp χ hχ f hf hMf Ψ hprim hagree,
    artinRay_inverse_primitiveCompletedUnified_one_ne_zero F E ψ hψ hD hnp χ hχ f hf hMf Ψ hprim hagree,
    hL,hLi⟩

end
end ArtinMatthews.AbelianLocal

namespace ArtinMatthews.VaryingKummerAnalytic.ArtinRay
open NumberField RayClass
open OAI.SevenEighths.FiniteFourier
open scoped NumberField IsMulCommutative Classical
noncomputable section
variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
variable [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]
variable [NumberField.IsTotallyComplex K]
local instance unifiedBoundaryModulusNeZero : NeZero (discriminantDegreeModulus K L) :=
  ⟨(discriminantDegreeModulus_pos K L).ne'⟩

theorem discriminantDegree_exists_primitiveCompletedUnified_boundary_nonzero
    (χ : Gal(L/K) →* ℂˣ) (hχ : χ ≠ 1) :
    ∃ (f : Ideal (𝓞 K)) (hf : f ≠ ⊥)
      (_hMf : rationalModulusIdeal (𝓞 K) (discriminantDegreeModulus K L) ≤ f)
      (Ψ : EvenIdealRayCharacter K f) (hprim : IsPrimitiveOnIdeals Ψ.residue),
      Ψ.IsNonprincipal ∧
      f.absNorm ≤ (rationalModulusIdeal (𝓞 K) (discriminantDegreeModulus K L)).absNorm ∧
      (∀ I : primeToModulusIdeals (rationalIdealRayModulus K (discriminantDegreeModulus K L)),
        Ψ.idealHom (I:FractionalIdealGroup K) =
          GaloisIdealCharacter.idealHom K L χ (I:FractionalIdealGroup K)) ∧
      Ψ.primitiveCompletedUnified hf 0 ≠ 0 ∧ Ψ.primitiveCompletedUnified hf 1 ≠ 0 ∧
      Ψ.inverse.primitiveCompletedUnified hf 0 ≠ 0 ∧
      Ψ.inverse.primitiveCompletedUnified hf 1 ≠ 0 ∧
      Ψ.primitiveContinued hf hprim 1 ≠ 0 ∧
      Ψ.inverse.primitiveContinued hf (Ψ.inverse_isPrimitive hf hprim) 1 ≠ 0 := by
  simpa only [discriminantDegreeRayCharacter_idealHom] using
    AbelianLocal.artinRay_exists_primitiveCompletedUnified_boundary_nonzero K L
      (fun χ => discriminantDegreeRayCharacter (K := K) (L := L) χ)
      (fun _ => rfl) (discr_dvd_discriminantDegreeModulus K L)
      (fun χ hχ => discriminantDegreeRayCharacter_isNonprincipal χ hχ) χ hχ

end
end ArtinMatthews.VaryingKummerAnalytic.ArtinRay
