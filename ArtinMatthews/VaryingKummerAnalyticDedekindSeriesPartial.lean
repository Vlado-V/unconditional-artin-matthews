module

public import ArtinMatthews.VaryingKummerAnalyticDedekindSeries
public import ArtinMatthews.VaryingKummerAnalyticMixedPartialDedekind


set_option backward.privateInPublic true
@[expose] public section

/-! Actual convergence of the mixed-signature partial Dedekind series. -/

namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField FractionalIdeal
open scoped NumberField nonZeroDivisors Classical BigOperators ENNReal
noncomputable section

variable (K : Type*) [Field K] [NumberField K]

/-- The genuine ideal-class norm series is summable for every number field. -/
theorem mixedPartialDedekind_norm_summable
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℝ} (hs : 1 < s) :
    Summable (fun J : integralIdealClassFiber I =>
      (FractionalIdeal.absNorm J.1.val : ℝ) ^ (-s)) := by
  let f : integralIdealClassFiber I → integralFractionalIdeals K :=
    fun J => ⟨J.val, J.property.1⟩
  have hf : Function.Injective f := by
    intro J L h
    apply Subtype.ext
    exact congrArg (fun A : integralFractionalIdeals K => A.val) h
  let F : integralFractionalIdeals K → ℝ :=
    fun J => (FractionalIdeal.absNorm J.1.val : ℝ) ^ (-s)
  have hF : Summable F := integralFractionalIdeals_norm_summable (K := K) hs
  have hcomp : Summable (F ∘ f) := hF.comp_injective hf
  have heq : F ∘ f = (fun J : integralIdealClassFiber I =>
      (FractionalIdeal.absNorm J.1.val : ℝ) ^ (-s)) := by
    funext J
    rfl
  rw [heq] at hcomp
  exact hcomp

/-- The actual positive partial series appearing in the mixed theta Mellin
identity is finite on its genuine half-plane of convergence. -/
theorem mixedPartialDedekindPositive_ne_top
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℝ} (hs : 1 < s) :
    mixedPartialDedekindPositive K I s ≠ ⊤ := by
  rw [mixedPartialDedekindPositive, ← ENNReal.ofReal_tsum_of_nonneg
    (fun J : integralIdealClassFiber I =>
      Real.rpow_nonneg (fractionalIdeal_absNorm_pos J.val).le _)
    (mixedPartialDedekind_norm_summable K I hs)]
  exact ENNReal.ofReal_ne_top

theorem mixedPartialDedekindPositive_lt_top
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℝ} (hs : 1 < s) :
    mixedPartialDedekindPositive K I s < ⊤ :=
  lt_top_iff_ne_top.mpr (mixedPartialDedekindPositive_ne_top K I hs)

end
end ArtinMatthews.VaryingKummerAnalytic
