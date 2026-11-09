module

public import ArtinMatthews.SourceRayPrincipalContinuation
public import ArtinMatthews.IdealRayPrimitivePresentation
public import ArtinMatthews.VaryingKummerAnalyticHeckeFiniteEulerContinuation


set_option backward.privateInPublic true
@[expose] public section

/-! Actual primitive continuation with the old modulus retained.
The separate principal branch is the genuine conductor-deleted zeta. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField VaryingKummerAnalytic OAI.SevenEighths.FiniteFourier
open scoped NumberField Classical BigOperators nonZeroDivisors
noncomputable section
variable (F : Type) [Field F] [NumberField F]
variable {M : Ideal (𝓞 F)} (ψ : EvenIdealRayCharacter F M) (hM : M ≠ ⊥)

structure SourceRayPrimitiveDatum where
  modulus : IdealConductorModulus F
  character : EvenIdealRayCharacter F modulus.val
  primitive : IsPrimitiveOnIdeals character.residue
  old_le : M ≤ modulus.val
  norm_le : modulus.val.absNorm ≤ M.absNorm
  agrees : ∀ I : RayClass.primeToModulusIdeals (integralIdealRayModulus M hM),
    character.idealHom (I : FractionalIdealGroup F) = ψ.idealHom (I : FractionalIdealGroup F)

def sourceRayPrimitiveDatum : SourceRayPrimitiveDatum F ψ hM :=
  Classical.choice (by
    obtain ⟨f, hf, hMf, Ψ, hprim, hnorm, _, hagree⟩ := ψ.exists_primitive_idealCharacter hM
    exact ⟨⟨⟨f, hf⟩, Ψ, hprim, hMf, hnorm, hagree⟩⟩)

def sourceRayNonprincipalContinued : ℂ → ℂ :=
  let d := sourceRayPrimitiveDatum F ψ hM
  d.character.idealCoprimeContinued d.modulus.property d.primitive M

theorem sourceRayNonprincipalContinued_entire :
    Differentiable ℂ (sourceRayNonprincipalContinued F ψ hM) := by
  let d := sourceRayPrimitiveDatum F ψ hM
  exact d.character.idealCoprimeContinued_entire d.modulus.property d.primitive M

theorem sourceRayNonprincipalContinued_eq_dirichlet (hψ : ψ.IsNonprincipal) (s : ℂ)
    (hs : 1 < s.re) :
    sourceRayNonprincipalContinued F ψ hM s = ψ.dirichlet s := by
  let d := sourceRayPrimitiveDatum F ψ hM
  have hn := ψ.primitiveIdeal_isNonprincipal hM d.modulus.val d.old_le d.character d.agrees hψ
  change d.character.idealCoprimeContinued d.modulus.property d.primitive M s = _
  rw [d.character.idealCoprimeContinued_eq_dirichlet d.modulus.property d.primitive hn M hM hs,
    ψ.dirichlet_eq_ideal_tsum hs]
  apply tsum_congr
  intro I
  rw [EvenIdealRayCharacter.idealTerm_apply,
    ψ.primitiveIdeal_allCoefficient_mask hM d.modulus.val d.old_le d.character d.agrees]
  split_ifs <;> simp only [zero_mul]

theorem sourceRayNonprincipalContinued_zero_iff (s : ℂ) (hs : 0 < s.re) :
    sourceRayNonprincipalContinued F ψ hM s = 0 ↔
      let d := sourceRayPrimitiveDatum F ψ hM
      d.character.primitiveContinued d.modulus.property d.primitive s = 0 := by
  let d := sourceRayPrimitiveDatum F ψ hM
  exact d.character.idealCoprimeContinued_zero_iff d.modulus.property d.primitive M hs

def sourceRayContinued (s : ℂ) : ℂ :=
  if ψ.IsNonprincipal then sourceRayNonprincipalContinued F ψ hM s
    else principalExteriorZeta (sourceRayModulusPrimeSet F M) s

def sourceRayRegularizedContinued (s : ℂ) : ℂ :=
  if ψ.IsNonprincipal then (s - 1) * sourceRayNonprincipalContinued F ψ hM s
    else principalExteriorZetaRegularized (sourceRayModulusPrimeSet F M) s

theorem sourceRayContinued_eq_dirichlet (s : ℂ) (hs : 1 < s.re) :
    sourceRayContinued F ψ hM s = ψ.dirichlet s := by
  unfold sourceRayContinued
  split_ifs with h
  · exact sourceRayNonprincipalContinued_eq_dirichlet F ψ hM h s hs
  · exact (sourceRayPrincipal_dirichlet_eq_exteriorZeta F ψ hM h s hs).symm

theorem sourceRayRegularizedContinued_eq_mul (s : ℂ) (hs : s ≠ 1) :
    sourceRayRegularizedContinued F ψ hM s = (s - 1) * sourceRayContinued F ψ hM s := by
  unfold sourceRayRegularizedContinued sourceRayContinued
  split_ifs
  · rfl
  · exact principalExteriorZetaRegularized_eq _ hs

theorem sourceRayRegularizedContinued_eq_dirichlet (s : ℂ) (hs : 1 < s.re) :
    sourceRayRegularizedContinued F ψ hM s = (s - 1) * ψ.dirichlet s := by
  have hn : s ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at hs
    exact lt_irrefl _ hs
  rw [sourceRayRegularizedContinued_eq_mul F ψ hM s hn, sourceRayContinued_eq_dirichlet F ψ hM s hs]

theorem sourceRayRegularizedContinued_entire :
    Differentiable ℂ (sourceRayRegularizedContinued F ψ hM) := by
  by_cases hψ : ψ.IsNonprincipal
  · have he : sourceRayRegularizedContinued F ψ hM =
        fun s => (s - 1) * sourceRayNonprincipalContinued F ψ hM s := funext (fun _ => ite_eq_left hψ)
    rw [he]
    exact (differentiable_id.sub (differentiable_const (c := (1 : ℂ)))).mul
      (sourceRayNonprincipalContinued_entire F ψ hM)
  · have he : sourceRayRegularizedContinued F ψ hM =
        principalExteriorZetaRegularized (sourceRayModulusPrimeSet F M) := funext (fun _ => ite_eq_right hψ)
    rw [he]
    exact principalExteriorZetaRegularized_entire (sourceRayModulusPrimeSet F M)

theorem sourceRayContinued_differentiableOn :
    DifferentiableOn ℂ (sourceRayContinued F ψ hM) {s : ℂ | s ≠ 1} := by
  have H := (sourceRayRegularizedContinued_entire F ψ hM).differentiableOn.div
    ((differentiable_id.sub (differentiable_const (c := (1 : ℂ)))).differentiableOn)
    (fun s (hs : s ≠ 1) => sub_ne_zero.mpr hs)
  apply H.congr
  intro s hs
  change s ≠ 1 at hs
  change sourceRayContinued F ψ hM s = sourceRayRegularizedContinued F ψ hM s / (s - 1)
  rw [sourceRayRegularizedContinued_eq_mul F ψ hM s hs]
  exact (mul_div_cancel_left₀ _ (sub_ne_zero.mpr hs)).symm

theorem sourceRayPrincipalRegularizedContinued_one (hψ : ¬ ψ.IsNonprincipal) :
    sourceRayRegularizedContinued F ψ hM 1 =
      principalExteriorZetaResidue F (sourceRayModulusPrimeSet F M) := by
  rw [sourceRayRegularizedContinued, ite_eq_right hψ, principalExteriorZetaRegularized_one]

theorem sourceRayPrincipalRegularizedContinued_one_ne_zero (hψ : ¬ ψ.IsNonprincipal) :
    sourceRayRegularizedContinued F ψ hM 1 ≠ 0 := by
  rw [sourceRayPrincipalRegularizedContinued_one F ψ hM hψ]
  exact principalExteriorZetaResidue_ne_zero (sourceRayModulusPrimeSet F M)

end
end ArtinMatthews.SourceEulerAssembly
