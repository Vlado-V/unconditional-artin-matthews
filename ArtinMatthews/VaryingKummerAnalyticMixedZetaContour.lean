module

public import ArtinMatthews.VaryingKummerAnalyticMixedZetaZero
public import ArtinMatthews.VaryingKummerAnalyticMixedZetaLeft


set_option backward.privateInPublic true
@[expose] public section

/-! Contour estimates for the canonical continuation, including its analytic
value at zero. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Complex
open scoped Classical
noncomputable section
universe u
variable (K : Type u) [Field K] [NumberField K]

theorem mixedDedekindZeta_ne_zero_away {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hxi : mixedCompletedDedekindXi K s ≠ 0)
    (hga : ∀ w : InfinitePlace K, ∀ n : ℕ, (InfinitePlace.mult w : ℂ)*s/2 ≠ -(n : ℂ)) :
    mixedDedekindZeta K s ≠ 0 := by
  rw [mixedDedekindZeta_eq_continuation K hs0, mixedDedekindZetaContinuation_quotient]
  apply div_ne_zero hxi
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hs0 (sub_ne_zero.mpr hs1))
    (cpow_ne_zero_iff.mpr (Or.inl
      (Complex.ofReal_ne_zero.mpr (mixedDiscriminantScale_pos K).ne'))))
    (mixedGammaFactor_ne_zero_away K hga)

theorem mixedDedekindZeta_left_ne_zero {s : ℂ} (hs : s.re = -(1/2 : ℝ)) :
    mixedDedekindZeta K s ≠ 0 := by
  have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs
  have hs1 : s ≠ 1 := by intro h; norm_num [h] at hs
  exact mixedDedekindZeta_ne_zero_away K hs0 hs1
    (mixedCompletedDedekindXi_nonzero_left K (by rw [hs]; norm_num))
    (mixedGammaArguments_left_away K hs)

theorem exists_mixedDedekindZeta_left_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : Type u) [Field K] [NumberField K], ∀ s : ℂ,
      s.re = -(1/2 : ℝ) →
      ‖logDeriv (mixedDedekindZeta K) s‖ ≤
        C*(Real.log |(discr K : ℝ)| +
          (Module.finrank ℚ K : ℝ)*Real.log (|s.im|+2)) := by
  obtain ⟨C,hC,hbound⟩ := exists_mixedDedekind_left_logarithmic_bound.{u}
  refine ⟨C,hC,?_⟩
  intro K _ _ s hs
  rw [mixedDedekindZeta_logDeriv_eq_continuation K (by intro h; norm_num [h] at hs)]
  exact hbound K s hs

end
end ArtinMatthews.VaryingKummerAnalytic
