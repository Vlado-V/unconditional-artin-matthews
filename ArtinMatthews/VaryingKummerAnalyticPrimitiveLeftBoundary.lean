module

public import ArtinMatthews.VaryingKummerAnalyticPrimitiveUncompletedFunctionalEquation
public import ArtinMatthews.VaryingKummerAnalyticMixedGammaRatioGlobal
public import ArtinMatthews.VaryingKummerAnalyticPrimitiveReciprocal


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine conductor-uniform polynomial growth on Re(s)=-1/4.
The exact conductor factor comes from the proved inverse-character
functional equation, the Gamma ratio from its actual logarithmic derivative,
and the right-hand L bound from the actual ideal Euler logarithm. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Complex
open scoped NumberField nonZeroDivisors Classical
noncomputable section
namespace EvenIdealRayCharacter
variable {K : Type*} [Field K] [NumberField K] {M : Ideal (𝓞 K)}
variable (ψ : EvenIdealRayCharacter K M)

theorem dirichlet_norm_le_primitiveReciprocalBound {s : ℂ} (hs : 5/4 ≤ s.re) :
    ‖ψ.dirichlet s‖ ≤ primitiveReciprocalBound K := by
  rw [← ψ.exp_eulerLog_eq_dirichlet (show 1 < s.re by linarith),Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  exact (Complex.re_le_norm _).trans (ψ.eulerLog_norm_le hs)

theorem primitiveContinued_norm_le_right (hM : M ≠ ⊥)
    (hprim : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.residue)
    (hnp : ψ.IsNonprincipal) {s : ℂ} (hs : 5/4 ≤ s.re) :
    ‖ψ.primitiveContinued hM hprim s‖ ≤ primitiveReciprocalBound K := by
  rw [ψ.primitiveContinued_eq_dirichlet hM hprim hnp (by linarith : 1 < s.re)]
  exact ψ.dirichlet_norm_le_primitiveReciprocalBound hs

theorem primitiveContinued_left_line_norm (hM : M ≠ ⊥)
    (hprim : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.residue)
    (hnp : ψ.IsNonprincipal) (t : ℝ) :
    ‖ψ.primitiveContinued hM hprim ((-1/4 : ℂ)+(t : ℂ)*I)‖ =
      (mixedConductorScale K (integralIdealFractionalUnit M hM))^(3/2 : ℝ) *
        ‖mixedGammaLeftRatio K t‖ *
          ‖ψ.inverse.primitiveContinued hM (ψ.inverse_isPrimitive hM hprim)
            ((5/4 : ℂ)-(t : ℂ)*I)‖ := by
  obtain ⟨W,hW,hfe⟩ := ψ.primitiveContinued_left_functionalEquation hM hprim hnp
  have hA := mixedConductorScale_pos K (integralIdealFractionalUnit M hM)
  have ha : 1-((-1/4 : ℂ)+(t : ℂ)*I) = (5/4 : ℂ)-(t : ℂ)*I := by ring
  have hr : (1-2*((-1/4 : ℂ)+(t : ℂ)*I)).re = (3/2 : ℝ) := by norm_num
  rw [hfe _ (by norm_num),ha]
  simp only [norm_mul,hW,one_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hA,mixedGammaLeftRatio,hr]
  ring

end EvenIdealRayCharacter

theorem exists_primitiveContinued_left_boundary_bound
    (K : Type*) [Field K] [NumberField K] :
    ∃ (C : ℝ) (m : ℕ), 0 < C ∧
      ∀ {M : Ideal (𝓞 K)} (ψ : EvenIdealRayCharacter K M) (hM : M ≠ ⊥)
        (hprim : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.residue)
        (_hnp : ψ.IsNonprincipal) (t : ℝ),
        ‖ψ.primitiveContinued hM hprim ((-1/4 : ℂ)+(t : ℂ)*I)‖ ≤
          C * (mixedConductorScale K (integralIdealFractionalUnit M hM))^(3/2 : ℝ) *
            (|t|+2)^m := by
  obtain ⟨C,m,hC,hbound⟩ := exists_mixedGammaLeftRatio_polynomial_bound K
  refine ⟨C*primitiveReciprocalBound K,m,mul_pos hC (primitiveReciprocalBound_pos K),?_⟩
  intro M ψ hM hprim hnp t
  rw [ψ.primitiveContinued_left_line_norm hM hprim hnp]
  have hright := ψ.inverse.primitiveContinued_norm_le_right hM (ψ.inverse_isPrimitive hM hprim)
    (ψ.inverse_isNonprincipal hnp) (s := (5/4 : ℂ)-(t : ℂ)*I) (by norm_num)
  have H := mul_le_mul (hbound t) hright (norm_nonneg _)
    (mul_nonneg hC.le (by positivity : 0 ≤ (|t|+2)^m))
  have HA := mul_le_mul_of_nonneg_left H
    (Real.rpow_nonneg (mixedConductorScale_pos K (integralIdealFractionalUnit M hM)).le (3/2 : ℝ))
  convert HA using 1 <;> ring

end
end ArtinMatthews.VaryingKummerAnalytic
