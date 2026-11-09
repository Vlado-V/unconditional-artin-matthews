module

public import ArtinMatthews.VaryingKummerAnalyticMixedGammaAnalytic
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Calculus.FDeriv.Analytic


set_option backward.privateInPublic true
@[expose] public section

/-! The logarithmic derivative of the actual mixed Gamma factor. A single
universal bound on the fixed real interval [1/2,2] controls every number field
linearly in its degree. -/
namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField Set
open scoped Classical BigOperators Topology
noncomputable section
universe u

def mixedGammaAtom (s : ℂ) : ℂ :=
  (1/2 : ℂ) * (Real.pi : ℂ)^(-s) * Complex.Gamma s

theorem mixedGammaAtom_ne_zero {s : ℂ} (hs : 0 < s.re) :
    mixedGammaAtom s ≠ 0 := by
  apply mul_ne_zero
  · exact mul_ne_zero (by norm_num) (Complex.cpow_ne_zero_iff.mpr
      (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
  · exact Complex.Gamma_ne_zero_of_re_pos hs

theorem mixedGammaAtom_differentiableAt {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ mixedGammaAtom s := by
  have hg : DifferentiableAt ℂ Complex.Gamma s := by
    apply Complex.differentiableAt_Gamma
    intro m he
    rw [he] at hs
    simp only [Complex.neg_re, Complex.natCast_re] at hs
    exact (not_lt_of_ge (neg_nonpos.mpr (Nat.cast_nonneg m))) hs
  have hp : DifferentiableAt ℂ (fun z : ℂ => (Real.pi : ℂ)^(-z)) s :=
    (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => -z) s).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  exact (hp.const_mul (1/2)).mul hg

theorem mixedGammaAtom_logDeriv_continuousOn :
    ContinuousOn (logDeriv mixedGammaAtom) {s : ℂ | 0 < s.re} := by
  have ha : AnalyticOnNhd ℂ mixedGammaAtom {s : ℂ | 0 < s.re} :=
    (show DifferentiableOn ℂ mixedGammaAtom {s : ℂ | 0 < s.re} from
      fun _ hs => (mixedGammaAtom_differentiableAt hs).differentiableWithinAt).analyticOnNhd
      (isOpen_lt continuous_const Complex.continuous_re)
  exact ha.deriv.continuousOn.div ha.continuousOn (fun _ hs => mixedGammaAtom_ne_zero hs)

theorem mixedGammaAtom_logDeriv_bounded :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ, s ∈ Icc (1/2 : ℝ) 2 →
      ‖logDeriv mixedGammaAtom (s : ℂ)‖ ≤ C := by
  have hc : ContinuousOn (fun s : ℝ => logDeriv mixedGammaAtom (s : ℂ))
      (Icc (1/2 : ℝ) 2) := by
    apply mixedGammaAtom_logDeriv_continuousOn.comp Complex.continuous_ofReal.continuousOn
    intro s hs
    change 0 < s
    linarith [hs.1]
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  exact ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _),
    fun s hs => (hC s hs).trans (le_max_left _ _)⟩

variable (K : Type u) [Field K] [NumberField K]

theorem mixedGammaFactor_logDeriv_eq {s : ℂ} (hs : 0 < s.re) :
    logDeriv (mixedGammaFactor K) s =
      ∑ w : InfinitePlace K, ((InfinitePlace.mult w : ℂ)/2) *
        logDeriv mixedGammaAtom ((InfinitePlace.mult w : ℂ)*s/2) := by
  change logDeriv (fun z : ℂ => ∏ w : InfinitePlace K,
    mixedGammaAtom ((InfinitePlace.mult w : ℂ)*z/2)) s = _
  have hd (w : InfinitePlace K) : DifferentiableAt ℂ
      (fun z : ℂ => mixedGammaAtom ((InfinitePlace.mult w : ℂ)*z/2)) s := by
    have ha : DifferentiableAt ℂ mixedGammaAtom ((InfinitePlace.mult w : ℂ)*s/2) :=
      mixedGammaAtom_differentiableAt (mixedGammaArgument_re_pos K w hs)
    exact ha.comp s
      (show DifferentiableAt ℂ (fun z : ℂ => (InfinitePlace.mult w : ℂ)*z/2) s
        from by fun_prop)
  rw [logDeriv_fun_prod
    (s := Finset.univ) (x := s)
    (f := fun w : InfinitePlace K => fun z : ℂ =>
      mixedGammaAtom ((InfinitePlace.mult w : ℂ)*z/2))
    (fun w _ => mixedGammaAtom_ne_zero (mixedGammaArgument_re_pos K w hs))
    (fun w _ => hd w)]
  apply Finset.sum_congr rfl
  intro w _
  rw [logDeriv_fun_comp (f := mixedGammaAtom)
    (g := fun z : ℂ => (InfinitePlace.mult w : ℂ)*z/2) (x := s)
    (mixedGammaAtom_differentiableAt
    (mixedGammaArgument_re_pos K w hs))
    (show DifferentiableAt ℂ (fun z : ℂ => (InfinitePlace.mult w : ℂ)*z/2) s
      from by fun_prop)]
  have hd : deriv (fun z : ℂ => (InfinitePlace.mult w : ℂ)*z/2) s =
      (InfinitePlace.mult w : ℂ)/2 := by
    simp
  rw [hd, mul_comm]

end
end ArtinMatthews.VaryingKummerAnalytic
