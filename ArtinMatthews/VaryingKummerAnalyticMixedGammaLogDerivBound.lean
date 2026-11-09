module

public import ArtinMatthews.VaryingKummerAnalyticMixedGammaLogDeriv


set_option backward.privateInPublic true
@[expose] public section

/-! A universal linear-in-degree bound for the actual mixed archimedean factor. -/
namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField Set
open scoped Classical BigOperators Topology
noncomputable section
universe u

variable (K : Type u) [Field K] [NumberField K]

theorem mixedGammaFactor_logDeriv_norm_le {C σ : ℝ}
    (hC : ∀ s : ℝ, s ∈ Icc (1/2 : ℝ) 2 → ‖logDeriv mixedGammaAtom (s : ℂ)‖ ≤ C)
    (hσ : σ ∈ Icc (1 : ℝ) 2) :
    ‖logDeriv (mixedGammaFactor K) (σ : ℂ)‖ ≤
      ((Module.finrank ℚ K : ℝ)/2)*C := by
  rw [mixedGammaFactor_logDeriv_eq K (by simpa using (show 0 < σ by linarith [hσ.1]))]
  have hterm (w : InfinitePlace K) :
      ‖((InfinitePlace.mult w : ℂ)/2) *
        logDeriv mixedGammaAtom ((InfinitePlace.mult w : ℂ)*(σ : ℂ)/2)‖ ≤
        ((InfinitePlace.mult w : ℝ)/2)*C := by
    have hm₁ : (1 : ℝ) ≤ InfinitePlace.mult w := InfinitePlace.one_le_mult
    have hm₂ : (InfinitePlace.mult w : ℝ) ≤ 2 := by
      unfold InfinitePlace.mult
      split_ifs <;> norm_num
    have hm : ((InfinitePlace.mult w : ℝ)*σ/2) ∈ Icc (1/2 : ℝ) 2 := by
      constructor
      · nlinarith [mul_le_mul_of_nonneg_left hσ.1 (by linarith : 0 ≤ (InfinitePlace.mult w : ℝ))]
      · nlinarith [mul_le_mul_of_nonneg_left hσ.2 (by linarith : 0 ≤ (InfinitePlace.mult w : ℝ))]
    have hb : ‖logDeriv mixedGammaAtom
        ((InfinitePlace.mult w : ℂ)*(σ : ℂ)/2)‖ ≤ C := by
      simpa only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_natCast,
        Complex.ofReal_ofNat] using hC _ hm
    have hn : ‖(InfinitePlace.mult w : ℂ)/2‖ = (InfinitePlace.mult w : ℝ)/2 := by simp
    rw [norm_mul, hn]
    exact mul_le_mul_of_nonneg_left hb (by positivity)
  calc
    _ ≤ ∑ w : InfinitePlace K, ‖((InfinitePlace.mult w : ℂ)/2) *
        logDeriv mixedGammaAtom ((InfinitePlace.mult w : ℂ)*(σ : ℂ)/2)‖ := norm_sum_le _ _
    _ ≤ ∑ w : InfinitePlace K, ((InfinitePlace.mult w : ℝ)/2)*C :=
      Finset.sum_le_sum (fun w _ => hterm w)
    _ = _ := by
      rw [← Finset.sum_mul, ← Finset.sum_div]
      have hs : (∑ w : InfinitePlace K, (InfinitePlace.mult w : ℝ)) =
          (Module.finrank ℚ K : ℝ) := by exact_mod_cast InfinitePlace.sum_mult_eq (K := K)
      rw [hs]

theorem exists_mixedGammaFactor_logDeriv_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : Type u) [Field K] [NumberField K],
      ∀ σ : ℝ, σ ∈ Icc (1 : ℝ) 2 →
        ‖logDeriv (mixedGammaFactor K) (σ : ℂ)‖ ≤ C*(Module.finrank ℚ K : ℝ) := by
  obtain ⟨C,hC,hbound⟩ := mixedGammaAtom_logDeriv_bounded
  refine ⟨C,hC,fun K _ _ σ hσ => ?_⟩
  exact (mixedGammaFactor_logDeriv_norm_le K hbound hσ).trans (by
    have hn : (0 : ℝ) ≤ Module.finrank ℚ K := Nat.cast_nonneg _
    nlinarith)

end
end ArtinMatthews.VaryingKummerAnalytic
