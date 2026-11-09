module

public import ArtinMatthews.VaryingKummerAnalyticMixedZetaContour


set_option backward.privateInPublic true
@[expose] public section

/-! Exact comparison of the genuine zeta and completed-xi zero orders,
including every actual nontrivial zero and its multiplicity. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Complex Set Filter
open OAI.PrimeDegreePackets.AnalyticGrowth
open scoped Classical Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

omit [NumberField K] in
theorem mixedGammaArguments_nonneg_away {s : ℂ} (hs : 0 ≤ s.re) (hs0 : s ≠ 0) :
    ∀ w : InfinitePlace K, ∀ n : ℕ, (InfinitePlace.mult w : ℂ)*s/2 ≠ -(n : ℂ) := by
  intro w n he
  have hm : (0 : ℝ) < InfinitePlace.mult w := Nat.cast_pos.mpr (InfinitePlace.mult_pos (w := w))
  have hr := congrArg Complex.re he
  simp only [Complex.div_ofNat_re,Complex.mul_re,Complex.natCast_re,
    Complex.natCast_im,zero_mul,sub_zero,Complex.neg_re] at hr
  have hp : 0 ≤ (InfinitePlace.mult w : ℝ)*s.re/2 := by positivity
  have hn : n = 0 := by
    have hn' : (n : ℝ) = 0 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    exact_mod_cast hn'
  subst n
  have hm0 : (InfinitePlace.mult w : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (InfinitePlace.mult_pos (w := w)))
  have hne : (InfinitePlace.mult w : ℂ)*s/2 ≠ 0 :=
    div_ne_zero (mul_ne_zero hm0 hs0) (by norm_num)
  exact hne (by simpa using he)

theorem mixedDedekindZeta_order_eq_xi_away {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hga : ∀ w : InfinitePlace K, ∀ n : ℕ, (InfinitePlace.mult w : ℂ)*s/2 ≠ -(n : ℂ)) :
    meromorphicOrderAt (mixedDedekindZeta K) s =
      meromorphicOrderAt (mixedCompletedDedekindXi K) s := by
  let V : ℂ → ℂ := fun z => ((mixedDiscriminantScale K : ℂ)^z)⁻¹ *
    mixedInverseGammaFactor K z / z / (z-1)
  have hD : Differentiable ℂ (fun z : ℂ => ((mixedDiscriminantScale K : ℂ)^z)⁻¹) := by
    apply Differentiable.inv
    · exact differentiable_id.const_cpow
        (Or.inl (Complex.ofReal_ne_zero.mpr (mixedDiscriminantScale_pos K).ne'))
    · intro z
      exact cpow_ne_zero_iff.mpr
        (Or.inl (Complex.ofReal_ne_zero.mpr (mixedDiscriminantScale_pos K).ne'))
  have hv : AnalyticAt ℂ V s :=
    ((((hD.analyticAt s).mul ((mixedInverseGammaFactor_entire K).analyticAt s)).div
      analyticAt_id hs0).div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hs1))
  have hv0 : V s ≠ 0 := by
    apply div_ne_zero (div_ne_zero (mul_ne_zero ?_ ?_) hs0) (sub_ne_zero.mpr hs1)
    · exact inv_ne_zero (cpow_ne_zero_iff.mpr
        (Or.inl (Complex.ofReal_ne_zero.mpr (mixedDiscriminantScale_pos K).ne')))
    · exact inv_ne_zero (mixedGammaFactor_ne_zero_away K hga)
  have he : mixedDedekindZeta K =ᶠ[𝓝 s] V * mixedCompletedDedekindXi K := by
    filter_upwards [mixedDedekindZeta_eventually_eq_continuation K hs0] with z hz
    rw [hz]
    simp only [mixedDedekindZetaContinuation,mixedRegularizedDedekindZeta,Pi.mul_apply,V]
    ring
  rw [meromorphicOrderAt_congr (he.filter_mono nhdsWithin_le_nhds)]
  exact meromorphicOrderAt_mul_of_ne_zero hv hv0

theorem mixedDedekindZeta_order_at_xi_zero {ρ : ℂ}
    (hρ : mixedCompletedDedekindXi K ρ = 0) :
    meromorphicOrderAt (mixedDedekindZeta K) ρ =
      (zeroMultiplicity (mixedCompletedDedekindXi K) ρ : WithTop ℤ) := by
  have h0 : ρ ≠ 0 := by intro h; subst ρ; exact mixedCompletedDedekindXi_zero_ne_zero K hρ
  have h1 : ρ ≠ 1 := by intro h; subst ρ; exact mixedCompletedDedekindXi_one_ne_zero K hρ
  rw [mixedDedekindZeta_order_eq_xi_away K h0 h1
    (mixedGammaArguments_nonneg_away K (mixedCompletedDedekindXi_zeros_in_strip K ρ hρ).1 h0)]
  exact (WithTop.coe_untop₀_of_ne_top (entire_order_ne_top
    (mixedCompletedDedekindXi_entire K) (mixedCompletedDedekindXi_zero_ne_zero K) ρ)).symm

end
end ArtinMatthews.VaryingKummerAnalytic
