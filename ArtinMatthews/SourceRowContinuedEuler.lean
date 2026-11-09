module

public import ArtinMatthews.SourceRowExteriorRay
public import ArtinMatthews.SourceRayReciprocalContinuation


set_option backward.privateInPublic true
@[expose] public section

/-! Bind the primitive and regularized principal continuations to the
actual source Kummer row, the actual fixed twist, and the literal calF. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic QuadraticWeil
open scoped NumberField Classical BigOperators
noncomputable section
variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
variable (u : sourceRing F S₀) (hu : u ≠ 0)
local notation "S" => sourceHilbertSet F S₀
local notation "v" => sourceRowFieldUnit F S₀ u hu
local notation "N" => sixthKummerSharpIdeal S v
local notation "hN" => sixthKummerSharpIdeal_ne_zero S v
local notation "ψ" => sourceRowKummerRay F hζ S₀ u hu

def sourceRowNumeratorPrimitive : SourceRayPrimitiveDatum F ψ hN :=
  sourceRayPrimitiveDatum F ψ hN

theorem sourceRowNumeratorPrimitive_norm_le :
    (sourceRowNumeratorPrimitive F hζ S₀ u hu).modulus.val.absNorm ≤
      (sixthKummerFixedIdeal S).absNorm *
        sourcePrimeExponentNorm F S₀ (sourceElementExponents F S₀ u hu) :=
  (sourceRowNumeratorPrimitive F hζ S₀ u hu).norm_le.trans
    (sourceRowKummerSharpIdeal_norm_le F hζ S₀ u hu)

def sourceRowNumeratorContinued : ℂ → ℂ :=
  sourceRayContinued F ψ hN

theorem sourceRowNumeratorContinued_eq_dirichlet (w : ℂ) (hw : 1 < w.re) :
    sourceRowNumeratorContinued F hζ S₀ u hu w = (ψ).dirichlet w :=
  sourceRayContinued_eq_dirichlet F ψ hN w hw

theorem sourceRowNumeratorContinued_entire (hu₆ : ¬ ∃ a : F, a ^ 6 = (u : F)) :
    Differentiable ℂ (sourceRowNumeratorContinued F hζ S₀ u hu) := by
  have hψ := sourceRowKummerRay_isNonprincipal F hζ S₀ u hu hu₆
  have he : sourceRowNumeratorContinued F hζ S₀ u hu = sourceRayNonprincipalContinued F ψ hN :=
    funext (fun _ => ite_eq_left hψ)
  rw [he]
  exact sourceRayNonprincipalContinued_entire F ψ hN

variable {M : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F M) (hM : M ≠ ⊥)
local notation "ω" => sourceRowKummerTwist F hζ S₀ u hu η hM
local notation "hMN" => mul_ne_zero hM hN

def sourceRowTwistPrimitive : SourceRayPrimitiveDatum F ω hMN :=
  sourceRayPrimitiveDatum F ω hMN

theorem sourceRowTwistPrimitive_norm_le :
    (sourceRowTwistPrimitive F hζ S₀ u hu η hM).modulus.val.absNorm ≤
      M.absNorm * (sixthKummerFixedIdeal S).absNorm *
        sourcePrimeExponentNorm F S₀ (sourceElementExponents F S₀ u hu) :=
  (sourceRowTwistPrimitive F hζ S₀ u hu η hM).norm_le.trans
    (sourceRowKummerTwist_modulus_norm F S₀ hζ u hu (M := M))

def sourceRowTwistReciprocal : ℂ → ℂ :=
  sourceRayReciprocalContinued F ω hMN

theorem sourceRowTwistReciprocal_eq_dirichlet (s : ℂ) (hs : 1 < s.re) :
    sourceRowTwistReciprocal F hζ S₀ u hu η hM s = ((ω).dirichlet s)⁻¹ :=
  sourceRayReciprocalContinued_eq_dirichlet_inv F ω hMN s hs

theorem sourceRowTwistReciprocal_principal_one (hω : ¬ (ω).IsNonprincipal) :
    sourceRowTwistReciprocal F hζ S₀ u hu η hM 1 = 0 :=
  sourceRayReciprocalContinued_principal_one F ω hMN hω

theorem sourceRowTwistReciprocal_principal_differentiableAt_one (hω : ¬ (ω).IsNonprincipal) :
    DifferentiableAt ℂ (sourceRowTwistReciprocal F hζ S₀ u hu η hM) 1 :=
  sourceRayReciprocalContinued_principal_differentiableAt_one F ω hMN hω

theorem sourceRowTwistNonprincipal_zero_iff (s : ℂ) (hs : 0 < s.re) :
    sourceRayNonprincipalContinued F ω hMN s = 0 ↔
      let d := sourceRowTwistPrimitive F hζ S₀ u hu η hM
      d.character.primitiveContinued d.modulus.property d.primitive s = 0 :=
  sourceRayNonprincipalContinued_zero_iff F ω hMN s hs

def sourceRowEulerContinuation (q : ProbeCoordinates) : ℂ :=
  principalExteriorZeta S (6 * q.2.2) *
    sourceRowNumeratorContinued F hζ S₀ u hu q.2.1 *
    sourceRowTwistReciprocal F hζ S₀ u hu η hM q.1 *
    sourceGlobalCorrection F hζ S₀ η u hu q

theorem sourceRowEulerContinuation_initial
    (hS : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)
    (hcut : probePrimeCutoff F ⊆ S) (ξ w z : ℂ)
    (hξ : 2 < ξ.re) (hw : 2 < w.re) (hz : 1 / 6 < z.re) :
    sourceRowEulerContinuation F hζ S₀ u hu η hM (ξ, w, z) =
      sourceGlobalCalF F hζ S₀ hS η u ξ w z := by
  rw [sourceGlobalCalF_eq_Hecke_dirichlet (F := F) (S₀ := S₀) (hζ := hζ)
    (u := u) (hu := hu) (η := η) (hM := hM) hS hcut ξ w z hξ hw hz]
  unfold sourceRowEulerContinuation
  dsimp only
  rw [sourceRowNumeratorContinued_eq_dirichlet F hζ S₀ u hu w (by linarith),
    sourceRowTwistReciprocal_eq_dirichlet F hζ S₀ u hu η hM ξ (by linarith), div_eq_mul_inv]

end
end ArtinMatthews.SourceEulerAssembly
