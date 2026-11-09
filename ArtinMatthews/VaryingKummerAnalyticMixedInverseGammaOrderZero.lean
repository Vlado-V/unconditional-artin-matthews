module

public import ArtinMatthews.VaryingKummerAnalyticMixedZetaContinuationBase
public import Mathlib.Analysis.Meromorphic.Order


set_option backward.privateInPublic true
@[expose] public section

/-! Exact order at zero of the actual reciprocal archimedean factor.
The global factorization retains every real and complex infinite place. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Complex
open scoped Classical BigOperators
noncomputable section

lemma inverseGamma_eq_mul_shift (z : ℂ) :
    (Gamma z)⁻¹ = z * (Gamma (z+1))⁻¹ := by
  by_cases hz : z = 0
  · subst z
    simp
  · rw [Gamma_add_one z hz, mul_inv_rev]
    calc
      (Gamma z)⁻¹ = (z*z⁻¹) * (Gamma z)⁻¹ := by rw [mul_inv_cancel₀ hz,one_mul]
      _ = _ := by ring

variable (K : Type*) [Field K] [NumberField K]

/-- The entire factor left after extracting one zero per infinite place. -/
def mixedInverseGammaUnit (s : ℂ) : ℂ :=
  ∏ w : InfinitePlace K, (InfinitePlace.mult w : ℂ) *
    ((Real.pi : ℂ)^(-((InfinitePlace.mult w : ℂ)*s/2)))⁻¹ *
      (Gamma ((InfinitePlace.mult w : ℂ)*s/2+1))⁻¹

theorem mixedInverseGammaUnit_entire : Differentiable ℂ (mixedInverseGammaUnit K) := by
  have hG (w : InfinitePlace K) : Differentiable ℂ
      (fun z : ℂ => (Gamma ((InfinitePlace.mult w : ℂ)*z/2+1))⁻¹) := by
    simpa only [one_div,Function.comp_def] using differentiable_one_div_Gamma.comp
      (by fun_prop : Differentiable ℂ (fun z : ℂ => (InfinitePlace.mult w : ℂ)*z/2+1))
  have hP (w : InfinitePlace K) : Differentiable ℂ
      (fun z : ℂ => ((Real.pi : ℂ)^(-((InfinitePlace.mult w : ℂ)*z/2)))⁻¹) := by
    apply Differentiable.inv
    · exact (by fun_prop : Differentiable ℂ
        (fun z : ℂ => -((InfinitePlace.mult w : ℂ)*z/2))).const_cpow
        (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    · intro z
      exact cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  unfold mixedInverseGammaUnit
  fun_prop

theorem mixedInverseGammaUnit_zero :
    mixedInverseGammaUnit K 0 = ∏ w : InfinitePlace K, (InfinitePlace.mult w : ℂ) := by
  simp [mixedInverseGammaUnit]

theorem mixedInverseGammaUnit_zero_ne : mixedInverseGammaUnit K 0 ≠ 0 := by
  rw [mixedInverseGammaUnit_zero]
  apply Finset.prod_ne_zero_iff.mpr
  intro w _
  exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt (InfinitePlace.mult_pos (w := w)))

theorem mixedInverseGammaFactor_factorization (s : ℂ) :
    mixedInverseGammaFactor K s = s ^ Fintype.card (InfinitePlace K) *
      mixedInverseGammaUnit K s := by
  unfold mixedInverseGammaFactor mixedGammaFactor mixedInverseGammaUnit
  rw [← Finset.prod_inv_distrib]
  calc
    _ = ∏ w : InfinitePlace K, s * ((InfinitePlace.mult w : ℂ) *
        ((Real.pi : ℂ)^(-((InfinitePlace.mult w : ℂ)*s/2)))⁻¹ *
        (Gamma ((InfinitePlace.mult w : ℂ)*s/2+1))⁻¹) := by
      apply Finset.prod_congr rfl
      intro w _
      rw [mul_inv_rev,mul_inv_rev,inverseGamma_eq_mul_shift]
      norm_num
      ring
    _ = _ := by rw [Finset.prod_mul_distrib]; simp

theorem mixedInverseGammaFactor_analyticOrder_zero :
    analyticOrderAt (mixedInverseGammaFactor K) 0 =
      (Fintype.card (InfinitePlace K) : ℕ∞) := by
  have hF : mixedInverseGammaFactor K =
      (fun s : ℂ => s ^ Fintype.card (InfinitePlace K)) * mixedInverseGammaUnit K :=
    funext (mixedInverseGammaFactor_factorization K)
  have hP : AnalyticAt ℂ (fun s : ℂ => s ^ Fintype.card (InfinitePlace K)) 0 := by
    fun_prop
  rw [hF, analyticOrderAt_mul hP ((mixedInverseGammaUnit_entire K).analyticAt 0),
    ((mixedInverseGammaUnit_entire K).analyticAt 0).analyticOrderAt_eq_zero.mpr
      (mixedInverseGammaUnit_zero_ne K),add_zero]
  exact hP.analyticOrderAt_eq_natCast.mpr
    ⟨fun _ => 1, by fun_prop, by simp, by simp⟩

theorem mixedInverseGammaFactor_meromorphicOrder_zero :
    meromorphicOrderAt (mixedInverseGammaFactor K) 0 =
      (InfinitePlace.nrRealPlaces K + InfinitePlace.nrComplexPlaces K : ℕ) := by
  rw [((mixedInverseGammaFactor_entire K).analyticAt 0).meromorphicOrderAt_eq,
    mixedInverseGammaFactor_analyticOrder_zero,ENat.map_natCast,
    InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]
  simp

end
end ArtinMatthews.VaryingKummerAnalytic
