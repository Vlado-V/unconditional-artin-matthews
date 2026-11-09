module

public import ArtinMatthews.VaryingKummerAnalyticMixedGammaVertical


set_option backward.privateInPublic true
@[expose] public section

/-! Logarithmic derivative identities for the actual mixed Gamma factor at
all points where its Gamma arguments avoid the nonpositive integers. -/
namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField
open scoped Classical BigOperators
noncomputable section
universe u

theorem mixedGammaAtom_ne_zero_away {s : ℂ} (hs : ∀ n : ℕ, s ≠ -(n : ℂ)) :
    mixedGammaAtom s ≠ 0 := by
  apply mul_ne_zero
  · exact mul_ne_zero (by norm_num) (Complex.cpow_ne_zero_iff.mpr
      (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
  · exact Complex.Gamma_ne_zero hs

theorem mixedGammaAtom_differentiableAt_away {s : ℂ} (hs : ∀ n : ℕ, s ≠ -(n : ℂ)) :
    DifferentiableAt ℂ mixedGammaAtom s := by
  have hg : DifferentiableAt ℂ Complex.Gamma s :=
    Complex.differentiableAt_Gamma s hs
  have hp : DifferentiableAt ℂ (fun z : ℂ => (Real.pi : ℂ)^(-z)) s :=
    (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => -z) s).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  exact (hp.const_mul (1/2)).mul hg

theorem mixedGammaAtom_logDeriv_eq_away {s : ℂ} (hs : ∀ n : ℕ, s ≠ -(n : ℂ)) :
    logDeriv mixedGammaAtom s = Complex.digamma s - Complex.log (Real.pi : ℂ) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  let p : ℂ → ℂ := fun z => (Real.pi : ℂ)^(-z)
  have hpne : p s ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hpi)
  have hp := ((hasDerivAt_id s).neg).const_cpow (Or.inl hpi)
  have hplog : logDeriv p s = -Complex.log (Real.pi : ℂ) := by
    rw [logDeriv_apply,
      show deriv p s = p s * Complex.log (Real.pi : ℂ) * (-1) from hp.deriv]
    field_simp
  have hgd : DifferentiableAt ℂ Complex.Gamma s :=
    Complex.differentiableAt_Gamma s hs
  have he : mixedGammaAtom = fun z => (1/2 : ℂ)*(p z*Complex.Gamma z) := by
    funext z
    dsimp [mixedGammaAtom,p]
    ring
  rw [he, logDeriv_const_mul s (1/2) (by norm_num),
    logDeriv_fun_mul (f := p) (g := Complex.Gamma) s hpne
      (Complex.Gamma_ne_zero hs) hp.differentiableAt hgd, hplog]
  change -Complex.log (Real.pi : ℂ) + Complex.digamma s = _
  ring


variable (K : Type u) [Field K] [NumberField K]

theorem mixedGammaFactor_logDeriv_eq_away {s : ℂ} (hs : ∀ w : InfinitePlace K, ∀ n : ℕ,
      (InfinitePlace.mult w : ℂ)*s/2 ≠ -(n : ℂ)) :
    logDeriv (mixedGammaFactor K) s =
      ∑ w : InfinitePlace K, ((InfinitePlace.mult w : ℂ)/2) *
        logDeriv mixedGammaAtom ((InfinitePlace.mult w : ℂ)*s/2) := by
  change logDeriv (fun z : ℂ => ∏ w : InfinitePlace K,
    mixedGammaAtom ((InfinitePlace.mult w : ℂ)*z/2)) s = _
  have hd (w : InfinitePlace K) : DifferentiableAt ℂ
      (fun z : ℂ => mixedGammaAtom ((InfinitePlace.mult w : ℂ)*z/2)) s := by
    have ha : DifferentiableAt ℂ mixedGammaAtom ((InfinitePlace.mult w : ℂ)*s/2) :=
      mixedGammaAtom_differentiableAt_away (hs w)
    exact ha.comp s
      (show DifferentiableAt ℂ (fun z : ℂ => (InfinitePlace.mult w : ℂ)*z/2) s
        from by fun_prop)
  rw [logDeriv_fun_prod
    (s := Finset.univ) (x := s)
    (f := fun w : InfinitePlace K => fun z : ℂ =>
      mixedGammaAtom ((InfinitePlace.mult w : ℂ)*z/2))
    (fun w _ => mixedGammaAtom_ne_zero_away (hs w))
    (fun w _ => hd w)]
  apply Finset.sum_congr rfl
  intro w _
  rw [logDeriv_fun_comp (f := mixedGammaAtom)
    (g := fun z : ℂ => (InfinitePlace.mult w : ℂ)*z/2) (x := s)
    (mixedGammaAtom_differentiableAt_away
    (hs w))
    (show DifferentiableAt ℂ (fun z : ℂ => (InfinitePlace.mult w : ℂ)*z/2) s
      from by fun_prop)]
  have hd : deriv (fun z : ℂ => (InfinitePlace.mult w : ℂ)*z/2) s =
      (InfinitePlace.mult w : ℂ)/2 := by
    simp
  rw [hd, mul_comm]
theorem mixedGammaFactor_logDeriv_norm_le_of_bounds_away
    (K : Type*) [Field K] [NumberField K] {s : ℂ} (hs : ∀ w : InfinitePlace K, ∀ n : ℕ,
      (InfinitePlace.mult w : ℂ)*s/2 ≠ -(n : ℂ)) {B : ℝ}
    (hb : ∀ w : InfinitePlace K,
      ‖logDeriv mixedGammaAtom ((InfinitePlace.mult w : ℂ)*s/2)‖ ≤ B) :
    ‖logDeriv (mixedGammaFactor K) s‖ ≤ ((Module.finrank ℚ K : ℝ)/2)*B := by
  rw [mixedGammaFactor_logDeriv_eq_away K hs]
  calc
    _ ≤ ∑ w : InfinitePlace K, ‖((InfinitePlace.mult w : ℂ)/2) *
        logDeriv mixedGammaAtom ((InfinitePlace.mult w : ℂ)*s/2)‖ := norm_sum_le _ _
    _ ≤ ∑ w : InfinitePlace K, ((InfinitePlace.mult w : ℝ)/2)*B := by
      apply Finset.sum_le_sum
      intro w _
      have hn : ‖(InfinitePlace.mult w : ℂ)/2‖ = (InfinitePlace.mult w : ℝ)/2 := by simp
      rw [norm_mul, hn]
      exact mul_le_mul_of_nonneg_left (hb w) (by positivity)
    _ = _ := by
      rw [← Finset.sum_mul, ← Finset.sum_div]
      have he : (∑ w : InfinitePlace K, (InfinitePlace.mult w : ℝ)) =
          (Module.finrank ℚ K : ℝ) := by
        exact_mod_cast InfinitePlace.sum_mult_eq (K := K)
      rw [he]

end
end ArtinMatthews.VaryingKummerAnalytic
