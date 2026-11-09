module

public import ArtinMatthews.VaryingKummerAnalyticPrimitiveUncompletedFunctionalEquation
public import ArtinMatthews.VaryingKummerAnalyticMixedInverseGammaStripGrowth


set_option backward.privateInPublic true
@[expose] public section

/-! Growth in the actual primitive convexity strip. The completion supplies
subquadratic growth; reciprocal Gamma growth is derived separately from its
actual logarithmic derivative. Constants here may depend on the character,
as permitted for the growth hypothesis of the maximum principle. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Complex Filter
open scoped NumberField nonZeroDivisors Classical Topology
noncomputable section
namespace EvenIdealRayCharacter
variable {K : Type*} [Field K] [NumberField K] {M : Ideal (𝓞 K)}
variable (ψ : EvenIdealRayCharacter K M) (hM : M ≠ ⊥)
variable (hprim : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.residue)
variable (hnp : ψ.IsNonprincipal)
include hnp

theorem primitiveContinued_convexity_strip_growth :
    ∃ C D R : ℝ, 0 < C ∧ 0 < D ∧ ∀ σ : ℝ,
      -(1/4 : ℝ) ≤ σ → σ ≤ 5/4 → ∀ t : ℝ, R ≤ |t| →
      ‖ψ.primitiveContinued hM hprim ((σ : ℂ)+(t : ℂ)*I)‖ ≤
        C*Real.exp (D*(|t|+2)^2) := by
  obtain ⟨C,D,hC,hD,hGamma⟩ := exists_mixedInverseGammaFactor_strip_growth K
  obtain ⟨R,hR⟩ := eventually_atTop.mp
    (ψ.primitiveCompletedUnified_hasSubquadraticGrowth hM hprim 1 zero_lt_one)
  let A := mixedConductorScale K (integralIdealFractionalUnit M hM)
  have hA : 0 < A := mixedConductorScale_pos K (integralIdealFractionalUnit M hM)
  let CA := Real.exp (2*|Real.log A|)
  refine ⟨CA*C,D+1,max 1 R,mul_pos (Real.exp_pos _) hC,by linarith,?_⟩
  intro σ hσ hσ' t ht
  have hsabs : |σ| ≤ 2 := abs_le.mpr ⟨by linarith,by linarith⟩
  have hscale : ‖(A : ℂ)^(-((σ : ℂ)+(t : ℂ)*I))‖ ≤ CA := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hA]
    simp only [neg_re,add_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,mul_zero,zero_mul,sub_zero,add_zero]
    rw [Real.rpow_def_of_pos hA]
    apply Real.exp_le_exp.mpr
    calc
      Real.log A*(-σ) ≤ |Real.log A*(-σ)| := le_abs_self _
      _ = |Real.log A| * |σ| := by rw [abs_mul,abs_neg]
      _ ≤ |Real.log A| * 2 := mul_le_mul_of_nonneg_left hsabs (abs_nonneg _)
      _ = _ := by ring
  have hz : ‖(σ : ℂ)+(t : ℂ)*I‖ ≤ |t|+2 := by
    calc
      _ ≤ ‖(σ : ℂ)‖+‖(t : ℂ)*I‖ := norm_add_le _ _
      _ = |σ|+|t| := by simp
      _ ≤ _ := by linarith
  have hcomplete := hR (|t|+2) (by linarith [le_max_right (1 : ℝ) R])
    ((σ : ℂ)+(t : ℂ)*I) hz
  simp only [one_mul] at hcomplete
  have hgam := hGamma σ hσ hσ' t (by linarith [le_max_left (1 : ℝ) R])
  rw [ψ.primitiveContinued_eq_unified_inverseGamma hM hprim hnp]
  change ‖(A : ℂ)^(-((σ : ℂ)+(t : ℂ)*I)) *
    mixedInverseGammaFactor K ((σ : ℂ)+(t : ℂ)*I) *
      ψ.primitiveCompletedUnified hM ((σ : ℂ)+(t : ℂ)*I)‖ ≤ _
  rw [norm_mul,norm_mul]
  calc
    _ ≤ (CA*(C*Real.exp (D*(|t|+2)^2)))*Real.exp ((|t|+2)^2) :=
      mul_le_mul (mul_le_mul hscale hgam (norm_nonneg _) (Real.exp_pos _).le)
        hcomplete (norm_nonneg _) (by positivity)
    _ = (CA*C)*(Real.exp (D*(|t|+2)^2)*Real.exp ((|t|+2)^2)) := by ring
    _ = _ := by
      rw [← Real.exp_add]
      congr 1
      congr 1
      ring

end EvenIdealRayCharacter
end
end ArtinMatthews.VaryingKummerAnalytic
