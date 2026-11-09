module

public import ArtinMatthews.VaryingKummerAnalyticMixedZetaContinuation
public import ArtinMatthews.VaryingKummerAnalyticMixedGammaAway
public import ArtinMatthews.VaryingKummerAnalyticMixedXiLogDeriv
public import ArtinMatthews.VaryingKummerAnalyticMixedXiZeroStrip


set_option backward.privateInPublic true
@[expose] public section

/-! Exact logarithmic functional equation of the genuine continued Dedekind
zeta, including the actual mixed archimedean factors. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Complex
open scoped Classical BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem mixedGammaFactor_ne_zero_away {s : ℂ}
    (hs : ∀ w : InfinitePlace K, ∀ n : ℕ, (InfinitePlace.mult w : ℂ)*s/2 ≠ -(n : ℂ)) :
    mixedGammaFactor K s ≠ 0 := by
  change (∏ w : InfinitePlace K, mixedGammaAtom ((InfinitePlace.mult w : ℂ)*s/2)) ≠ 0
  exact Finset.prod_ne_zero_iff.mpr (fun w _ => mixedGammaAtom_ne_zero_away (hs w))

theorem mixedGammaFactor_differentiableAt_away {s : ℂ}
    (hs : ∀ w : InfinitePlace K, ∀ n : ℕ, (InfinitePlace.mult w : ℂ)*s/2 ≠ -(n : ℂ)) :
    DifferentiableAt ℂ (mixedGammaFactor K) s := by
  have h (w : InfinitePlace K) : DifferentiableAt ℂ
      (fun z : ℂ => mixedGammaAtom ((InfinitePlace.mult w : ℂ)*z/2)) s := by
    have ha : DifferentiableAt ℂ mixedGammaAtom ((InfinitePlace.mult w : ℂ)*s/2) :=
      mixedGammaAtom_differentiableAt_away (hs w)
    exact ha.comp s
      (show DifferentiableAt ℂ (fun z : ℂ => (InfinitePlace.mult w : ℂ)*z/2) s from by fun_prop)
  change DifferentiableAt ℂ (fun z : ℂ => ∏ w : InfinitePlace K,
    mixedGammaAtom ((InfinitePlace.mult w : ℂ)*z/2)) s
  fun_prop

theorem mixedDedekindZetaContinuation_quotient (s : ℂ) :
    mixedDedekindZetaContinuation K s = mixedCompletedDedekindXi K s /
      (s*(s-1)*(mixedDiscriminantScale K : ℂ)^s*mixedGammaFactor K s) := by
  simp only [mixedDedekindZetaContinuation, mixedRegularizedDedekindZeta,
    mixedInverseGammaFactor, div_eq_mul_inv, mul_inv_rev]
  ring

theorem mixedDedekindZetaContinuation_logDeriv {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hxi : mixedCompletedDedekindXi K s ≠ 0)
    (hga : ∀ w : InfinitePlace K, ∀ n : ℕ, (InfinitePlace.mult w : ℂ)*s/2 ≠ -(n : ℂ)) :
    logDeriv (mixedDedekindZetaContinuation K) s =
      logDeriv (mixedCompletedDedekindXi K) s - 1/s - 1/(s-1) -
        (Real.log (mixedDiscriminantScale K) : ℂ) - logDeriv (mixedGammaFactor K) s := by
  have hd : (mixedDiscriminantScale K : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (mixedDiscriminantScale_pos K).ne'
  have hdp : (mixedDiscriminantScale K : ℂ)^s ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hd)
  have hg := mixedGammaFactor_ne_zero_away K hga
  have hdc : DifferentiableAt ℂ (fun z : ℂ => (mixedDiscriminantScale K : ℂ)^z) s :=
    differentiableAt_id.const_cpow (Or.inl hd)
  have hdg := mixedGammaFactor_differentiableAt_away K hga
  have hs1' := sub_ne_zero.mpr hs1
  have he : mixedDedekindZetaContinuation K = fun z : ℂ => mixedCompletedDedekindXi K z /
      (z*(z-1)*(mixedDiscriminantScale K : ℂ)^z*mixedGammaFactor K z) :=
    funext (mixedDedekindZetaContinuation_quotient K)
  rw [he, logDeriv_fun_div (f := mixedCompletedDedekindXi K)
    (g := fun z : ℂ => z*(z-1)*(mixedDiscriminantScale K : ℂ)^z*mixedGammaFactor K z)
    s hxi (mul_ne_zero (mul_ne_zero (mul_ne_zero hs0 hs1') hdp) hg)
    (mixedCompletedDedekindXi_entire K s)
    (((differentiableAt_id.mul (differentiableAt_id.sub_const 1)).mul hdc).mul hdg),
    logDeriv_fun_mul
      (f := fun z : ℂ => z*(z-1)*(mixedDiscriminantScale K : ℂ)^z)
      (g := mixedGammaFactor K) s (mul_ne_zero (mul_ne_zero hs0 hs1') hdp) hg
      ((differentiableAt_id.mul (differentiableAt_id.sub_const 1)).mul hdc) hdg,
    logDeriv_fun_mul (f := fun z : ℂ => z*(z-1))
      (g := fun z : ℂ => (mixedDiscriminantScale K : ℂ)^z) s
      (mul_ne_zero hs0 hs1') hdp
      (differentiableAt_id.mul (differentiableAt_id.sub_const 1)) hdc,
    logDeriv_fun_mul (f := fun z : ℂ => z) (g := fun z : ℂ => z-1)
      s hs0 hs1' differentiableAt_id (differentiableAt_id.sub_const 1),
    logDeriv_id', Complex.logDeriv_const_cpow hd]
  have hsub : logDeriv (fun z : ℂ => z-1) s = 1/(s-1) := by
    rw [logDeriv_apply, ((hasDerivAt_id' s).sub_const 1).deriv]
  rw [hsub, ← Complex.ofReal_log (mixedDiscriminantScale_pos K).le]
  ring

/-- Reflection into the convergent half-plane. No Euler-product estimate or
zero-free theorem is assumed: the right-hand zeta is the actual series. -/
theorem mixedDedekindZetaContinuation_logDeriv_left {s : ℂ} (hs : s.re < 0)
    (hga : ∀ w : InfinitePlace K, ∀ n : ℕ, (InfinitePlace.mult w : ℂ)*s/2 ≠ -(n : ℂ)) :
    logDeriv (mixedDedekindZetaContinuation K) s =
      -(2*(Real.log (mixedDiscriminantScale K) : ℂ)) -
        logDeriv (mixedGammaFactor K) s - logDeriv (mixedGammaFactor K) (1-s) -
        logDeriv (NumberField.dedekindZeta K) (1-s) := by
  have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs
  have hs1 : s ≠ 1 := by intro h; norm_num [h] at hs
  have ht : 1 < (1-s).re := by simp only [sub_re,one_re]; linarith
  have hfe := OAI.PrimeDegreePackets.AnalyticGrowth.logDeriv_reflection
    (mixedCompletedDedekindXi_entire K)
    (fun z => (mixedCompletedDedekindXi_functional_equation K z).symm) s
  rw [mixedDedekindZetaContinuation_logDeriv K hs0 hs1
    (mixedCompletedDedekindXi_nonzero_left K hs) hga]
  rw [mixedCompletedDedekindXi_logDeriv K ht] at hfe
  have hneg : 1/(1-s) = -(1/(s-1)) := by rw [show 1-s = -(s-1) by ring, div_neg]
  have hsub : 1/((1-s)-1) = -(1/s) := by rw [show (1-s)-1 = -s by ring, div_neg]
  rw [hneg,hsub] at hfe
  linear_combination hfe

end
end ArtinMatthews.VaryingKummerAnalytic
