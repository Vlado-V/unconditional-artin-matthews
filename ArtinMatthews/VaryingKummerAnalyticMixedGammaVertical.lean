module

public import ArtinMatthews.VaryingKummerAnalyticMixedGammaAtomLog
public import ArtinMatthews.ReusedDigammaSeries


set_option backward.privateInPublic true
@[expose] public section

/-! Degree-uniform logarithmic growth of the actual mixed Gamma factor on
the full vertical strip 1 <= Re(s) <= 2. -/
namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField Set
open scoped Classical BigOperators
noncomputable section
universe u

theorem mixedGammaAtom_logarithmic_bound :
    ∃ B : ℝ, 0 < B ∧ ∀ s : ℂ, 1/2 ≤ s.re → s.re ≤ 2 →
      ‖logDeriv mixedGammaAtom s‖ ≤ B*Real.log (|s.im|+2) := by
  obtain ⟨C,hC,hb⟩ := Complex.exists_norm_digamma_le_log
    (a := 1/2) (b := 2) (by norm_num)
  let D := |Real.log Real.pi|/Real.log 2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨C+D+1,by positivity,?_⟩
  intro s hs hs'
  have hlog : Real.log 2 ≤ Real.log (|s.im|+2) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg s.im])
  have hlogpos : 0 < Real.log (|s.im|+2) := hlog2.trans_le hlog
  have hDlog : |Real.log Real.pi| ≤ D*Real.log (|s.im|+2) := by
    have hm := mul_le_mul_of_nonneg_left hlog hD
    dsimp [D] at hm
    rwa [div_mul_cancel₀ _ hlog2.ne'] at hm
  have hpi : ‖Complex.log (Real.pi : ℂ)‖ = |Real.log Real.pi| := by
    rw [← Complex.ofReal_log Real.pi_pos.le, Complex.norm_real, Real.norm_eq_abs]
  rw [mixedGammaAtom_logDeriv_eq (by linarith : 0 < s.re)]
  calc
    _ ≤ ‖Complex.digamma s‖ + ‖Complex.log (Real.pi : ℂ)‖ := norm_sub_le _ _
    _ ≤ C*Real.log (|s.im|+2) + |Real.log Real.pi| := by rw [hpi]; gcongr; exact hb s hs hs'
    _ ≤ (C+D+1)*Real.log (|s.im|+2) := by nlinarith

theorem exists_mixedGammaFactor_vertical_logarithmic_bound :
    ∃ B : ℝ, 0 < B ∧ ∀ (K : Type u) [Field K] [NumberField K],
      ∀ s : ℂ, 1 ≤ s.re → s.re ≤ 2 →
        ‖logDeriv (mixedGammaFactor K) s‖ ≤
          B*(Module.finrank ℚ K : ℝ)*Real.log (|s.im|+2) := by
  obtain ⟨B,hB,hbound⟩ := mixedGammaAtom_logarithmic_bound
  refine ⟨B,hB,?_⟩
  intro K _ _ s hs hs'
  have hlog : 0 < Real.log (|s.im|+2) := Real.log_pos (by linarith [abs_nonneg s.im])
  have hb (w : InfinitePlace K) :
      ‖logDeriv mixedGammaAtom ((InfinitePlace.mult w : ℂ)*s/2)‖ ≤
        B*Real.log (|s.im|+2) := by
    have hm₁ : (1 : ℝ) ≤ InfinitePlace.mult w := InfinitePlace.one_le_mult
    have hm₂ : (InfinitePlace.mult w : ℝ) ≤ 2 := by
      unfold InfinitePlace.mult
      split_ifs <;> norm_num
    have hm₀ : (0 : ℝ) ≤ InfinitePlace.mult w := Nat.cast_nonneg _
    have hre : (((InfinitePlace.mult w : ℂ)*s/2).re) =
        (InfinitePlace.mult w : ℝ)*s.re/2 := by simp
    have him : (((InfinitePlace.mult w : ℂ)*s/2).im) =
        (InfinitePlace.mult w : ℝ)*s.im/2 := by simp
    have harg₁ : 1/2 ≤ (((InfinitePlace.mult w : ℂ)*s/2).re) := by
      rw [hre]
      nlinarith [mul_le_mul_of_nonneg_left hs hm₀]
    have harg₂ : (((InfinitePlace.mult w : ℂ)*s/2).re) ≤ 2 := by
      rw [hre]
      nlinarith [mul_le_mul_of_nonneg_left hs' hm₀]
    apply (hbound _ harg₁ harg₂).trans
    apply mul_le_mul_of_nonneg_left _ hB.le
    apply Real.log_le_log (by positivity)
    rw [him, abs_div, abs_mul, abs_of_nonneg hm₀]
    norm_num
    nlinarith [abs_nonneg s.im]
  apply (mixedGammaFactor_logDeriv_norm_le_of_bounds K (by linarith) hb).trans
  have hn : (0 : ℝ) ≤ Module.finrank ℚ K := Nat.cast_nonneg _
  have hp := mul_nonneg hn (mul_nonneg hB.le hlog.le)
  nlinarith

end
end ArtinMatthews.VaryingKummerAnalytic
