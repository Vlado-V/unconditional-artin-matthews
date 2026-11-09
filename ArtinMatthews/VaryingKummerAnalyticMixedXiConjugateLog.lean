module

public import ArtinMatthews.VaryingKummerAnalyticMixedXiReality
public import Mathlib.Analysis.Calculus.LogDeriv


set_option backward.privateInPublic true
@[expose] public section

/-! Conjugation of the actual xi logarithmic derivative and symmetric
zero-avoiding heights. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open Complex
open scoped ComplexConjugate
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem mixedCompletedDedekindXi_logDeriv_conj (s : ℂ) :
    logDeriv (mixedCompletedDedekindXi K) (conj s) =
      conj (logDeriv (mixedCompletedDedekindXi K) s) := by
  have he : conj ∘ mixedCompletedDedekindXi K ∘ conj = mixedCompletedDedekindXi K := by
    funext z
    simp only [Function.comp_apply, mixedCompletedDedekindXi_conj, starRingEnd_self_apply]
  have hd := congrFun (deriv_conj_conj (f := mixedCompletedDedekindXi K)) (conj s)
  rw [he] at hd
  simp only [Function.comp_apply,starRingEnd_self_apply] at hd
  rw [logDeriv_apply,logDeriv_apply,hd,mixedCompletedDedekindXi_conj,map_div₀]

theorem mixedCompletedDedekindXi_logDeriv_norm_neg_height (σ t : ℝ) :
    ‖logDeriv (mixedCompletedDedekindXi K) (⟨σ,-t⟩ : ℂ)‖ =
      ‖logDeriv (mixedCompletedDedekindXi K) (⟨σ,t⟩ : ℂ)‖ := by
  have he : (⟨σ,-t⟩ : ℂ) = conj (⟨σ,t⟩ : ℂ) := by apply Complex.ext <;> rfl
  rw [he,mixedCompletedDedekindXi_logDeriv_conj,norm_conj]

theorem mixedCompletedDedekindXi_symmetric_height_avoids {t : ℝ}
    (havoid : ∀ ρ : ℂ, mixedCompletedDedekindXi K ρ = 0 → 0 < |t-ρ.im|) :
    ∀ ρ : ℂ, mixedCompletedDedekindXi K ρ = 0 → |ρ.im| ≠ t := by
  intro ρ hρ he
  have ha := havoid ρ hρ
  have hb := havoid (conj ρ) (by rw [mixedCompletedDedekindXi_conj,hρ,map_zero])
  by_cases hi : 0 ≤ ρ.im
  · rw [abs_of_nonneg hi] at he
    rw [he,sub_self,abs_zero] at ha
    exact lt_irrefl _ ha
  · rw [abs_of_neg (lt_of_not_ge hi)] at he
    simp only [Complex.conj_im] at hb
    rw [← he,sub_self,abs_zero] at hb
    exact lt_irrefl _ hb

end
end ArtinMatthews.VaryingKummerAnalytic
