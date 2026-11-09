module

public import ArtinMatthews.SourceRayPrimitiveContinuation


set_option backward.privateInPublic true
@[expose] public section

/-! The reciprocal of a principal twist is extended through its simple
pole by the actual regularized Dedekind value. Nonprincipal twists keep
their literal primitive-continuation zeros and old modulus. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField VaryingKummerAnalytic Set
open scoped NumberField Classical BigOperators Topology
noncomputable section
variable (F : Type) [Field F] [NumberField F]
variable {M : Ideal (𝓞 F)} (ψ : EvenIdealRayCharacter F M) (hM : M ≠ ⊥)

def sourceRayReciprocalContinued (s : ℂ) : ℂ :=
  if ψ.IsNonprincipal then (sourceRayNonprincipalContinued F ψ hM s)⁻¹
    else (s - 1) / principalExteriorZetaRegularized (sourceRayModulusPrimeSet F M) s

theorem sourceRayReciprocalContinued_of_nonprincipal (hψ : ψ.IsNonprincipal) :
    sourceRayReciprocalContinued F ψ hM = fun s => (sourceRayNonprincipalContinued F ψ hM s)⁻¹ :=
  funext (fun _ => ite_eq_left hψ)

theorem sourceRayReciprocalContinued_of_principal (hψ : ¬ ψ.IsNonprincipal) :
    sourceRayReciprocalContinued F ψ hM =
      fun s => (s - 1) / principalExteriorZetaRegularized (sourceRayModulusPrimeSet F M) s :=
  funext (fun _ => ite_eq_right hψ)

theorem sourceRayReciprocalContinued_eq_inv (s : ℂ) (hs : s ≠ 1) :
    sourceRayReciprocalContinued F ψ hM s = (sourceRayContinued F ψ hM s)⁻¹ := by
  unfold sourceRayReciprocalContinued sourceRayContinued
  split_ifs
  · rfl
  · rw [principalExteriorZetaRegularized_eq _ hs, div_eq_mul_inv, mul_inv_rev]
    calc
      _ = (s - 1) * (s - 1)⁻¹ * (principalExteriorZeta (sourceRayModulusPrimeSet F M) s)⁻¹ := by ac_rfl
      _ = _ := by rw [mul_inv_cancel₀ (sub_ne_zero.mpr hs), one_mul]

theorem sourceRayReciprocalContinued_eq_dirichlet_inv (s : ℂ) (hs : 1 < s.re) :
    sourceRayReciprocalContinued F ψ hM s = (ψ.dirichlet s)⁻¹ := by
  have h : s ≠ 1 := by
    intro he
    rw [he, Complex.one_re] at hs
    exact lt_irrefl _ hs
  rw [sourceRayReciprocalContinued_eq_inv F ψ hM s h, sourceRayContinued_eq_dirichlet F ψ hM s hs]

theorem sourceRayReciprocalContinued_principal_one (hψ : ¬ ψ.IsNonprincipal) :
    sourceRayReciprocalContinued F ψ hM 1 = 0 := by
  rw [sourceRayReciprocalContinued, ite_eq_right hψ, sub_self, zero_div]

theorem sourceRayReciprocalContinued_principal_differentiableAt_one (hψ : ¬ ψ.IsNonprincipal) :
    DifferentiableAt ℂ (sourceRayReciprocalContinued F ψ hM) 1 := by
  have h := principalExteriorZetaResidue_ne_zero (sourceRayModulusPrimeSet F M)
  have hZ : principalExteriorZetaRegularized (sourceRayModulusPrimeSet F M) 1 ≠ 0 := by
    rw [principalExteriorZetaRegularized_one]
    exact h
  rw [sourceRayReciprocalContinued_of_principal F ψ hM hψ]
  exact ((differentiableAt_id.sub (differentiableAt_const (1 : ℂ))).div
      ((principalExteriorZetaRegularized_entire (sourceRayModulusPrimeSet F M)).differentiableAt)
      hZ : DifferentiableAt ℂ (fun s : ℂ => (s - 1) /
        principalExteriorZetaRegularized (sourceRayModulusPrimeSet F M) s) 1)

def sourceRayReciprocalDomain : Set ℂ :=
  if ψ.IsNonprincipal then {s | sourceRayNonprincipalContinued F ψ hM s ≠ 0}
    else {s | principalExteriorZetaRegularized (sourceRayModulusPrimeSet F M) s ≠ 0}

theorem sourceRayReciprocalDomain_isOpen : IsOpen (sourceRayReciprocalDomain F ψ hM) := by
  unfold sourceRayReciprocalDomain
  split_ifs
  · exact (isOpen_ne : IsOpen {z : ℂ | z ≠ 0}).preimage
      (sourceRayNonprincipalContinued_entire F ψ hM).continuous
  · exact (isOpen_ne : IsOpen {z : ℂ | z ≠ 0}).preimage
      (principalExteriorZetaRegularized_entire (sourceRayModulusPrimeSet F M)).continuous

theorem sourceRayReciprocalContinued_differentiableOn :
    DifferentiableOn ℂ (sourceRayReciprocalContinued F ψ hM) (sourceRayReciprocalDomain F ψ hM) := by
  by_cases hψ : ψ.IsNonprincipal
  · rw [sourceRayReciprocalDomain, ite_eq_left hψ, sourceRayReciprocalContinued_of_nonprincipal F ψ hM hψ]
    exact (sourceRayNonprincipalContinued_entire F ψ hM).differentiableOn.inv (fun _ h => h)
  · rw [sourceRayReciprocalDomain, ite_eq_right hψ, sourceRayReciprocalContinued_of_principal F ψ hM hψ]
    exact (differentiable_id.sub (differentiable_const (c := (1 : ℂ)))).differentiableOn.div
      (principalExteriorZetaRegularized_entire (sourceRayModulusPrimeSet F M)).differentiableOn
      (fun _ h => h)

end
end ArtinMatthews.SourceEulerAssembly
