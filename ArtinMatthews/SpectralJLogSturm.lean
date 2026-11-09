module

public import ArtinMatthews.MarkedMajorOscillatoryDerivatives
public import ArtinMatthews.SourceSturmSpectralPowers
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas


set_option backward.privateInPublic true
@[expose] public section

/-! Uniform logarithmic Sturm seminorms of the actual smooth oscillatory
family on each fixed compact interval. The constants are derived from
the fixed amplitude and phase. -/
namespace ArtinMatthews
open Set
open scoped BigOperators ContDiff
noncomputable section

def spectralJLogPotential (v : ℝ) : ℂ := (Real.exp (2*v) : ℂ)

def spectralJLogSturm (a : ℝ) (g : ℝ → ℂ) (v : ℝ) : ℂ :=
  deriv (deriv g) v + (a : ℂ)^2 * (spectralJLogPotential v * g v)

private theorem spectralJLogPotential_smooth :
    ContDiff ℝ ∞ spectralJLogPotential := by
  unfold spectralJLogPotential
  exact Complex.ofRealCLM.contDiff.comp
    (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id))

theorem spectralJLogSturm_smooth (a : ℝ) {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (spectralJLogSturm a g) := by
  have hg' := (contDiff_infty_iff_deriv.mp hg).2
  have hg'' := (contDiff_infty_iff_deriv.mp hg').2
  exact hg''.add (contDiff_const.mul (spectralJLogPotential_smooth.mul hg))

theorem spectralJLogSturm_iterate_smooth (a : ℝ) (n : ℕ) {g : ℝ → ℂ}
    (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (((spectralJLogSturm a)^[n]) g) := by
  induction n with
  | zero => exact hg
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact spectralJLogSturm_smooth a ih

theorem spectralJLogSturm_iterate_bound
    (A : ℝ → ℂ) (B : ℝ → ℝ) (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B)
    (K : Set ℝ) (hK : IsCompact K) (R : ℝ) (hR : 0 ≤ R) (n j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ a u v : ℝ, |a| ≤ R → v ∈ K →
      ‖iteratedDeriv j (((spectralJLogSturm a)^[n]) (markedOscillatoryFamily A B u)) v‖ ≤
        C*(1+|u|)^(j+2*n) := by
  induction n generalizing j with
  | zero =>
    obtain ⟨C,hC,hb⟩ := markedOscillatoryFamily_compact_derivative_bound A B hA hB K hK j
    refine ⟨C,hC,?_⟩
    intro a u v _ hv
    simpa only [Function.iterate_zero, id_eq, Nat.mul_zero, Nat.add_zero,
      norm_iteratedFDeriv_eq_norm_iteratedDeriv] using hb u v hv
  | succ n ih =>
    choose C hC hb using ih
    obtain ⟨M,hM,hMb⟩ := compact_norm_iteratedFDeriv_bound
      spectralJLogPotential spectralJLogPotential_smooth K hK j
    let S : ℝ := ∑ k ∈ Finset.range (j+1), (j.choose k : ℝ)*M*C (j-k)
    have hS : 0 ≤ S := Finset.sum_nonneg fun k _ =>
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hM.le) (hC _).le
    refine ⟨C (j+2)+R^2*S+1, by
      linarith [hC (j+2), mul_nonneg (sq_nonneg R) hS], ?_⟩
    intro a u v ha hv
    let g := ((spectralJLogSturm a)^[n]) (markedOscillatoryFamily A B u)
    let W := 1+|u|
    let N := j+2*(n+1)
    have hW : 1 ≤ W := by dsimp [W]; linarith [abs_nonneg u]
    have hg : ContDiff ℝ ∞ g := spectralJLogSturm_iterate_smooth a n
      (markedOscillatoryFamily_contDiff A B hA hB u)
    have hg' := (contDiff_infty_iff_deriv.mp hg).2
    have hg'' := (contDiff_infty_iff_deriv.mp hg').2
    have hproduct : ContDiff ℝ ∞ (fun y => spectralJLogPotential y*g y) :=
      spectralJLogPotential_smooth.mul hg
    have hsecond : ‖iteratedDeriv j (deriv (deriv g)) v‖ ≤ C (j+2)*W^N := by
      rw [← iteratedDeriv_succ', ← iteratedDeriv_succ']
      rw [show j+1+1 = j+2 by omega]
      simpa only [g, W, N, show j+2+2*n = j+2*(n+1) by omega]
        using hb (j+2) a u v ha hv
    have hprod :
        ‖iteratedDeriv j (fun y => spectralJLogPotential y*g y) v‖ ≤ S*W^N := by
      rw [iteratedDeriv_fun_mul (spectralJLogPotential_smooth.of_le (by simp)).contDiffAt
        (hg.of_le (by simp)).contDiffAt]
      calc
        _ ≤ ∑ k ∈ Finset.range (j+1),
            ‖(j.choose k : ℂ)*iteratedDeriv k spectralJLogPotential v*
              iteratedDeriv (j-k) g v‖ := norm_sum_le _ _
        _ ≤ ∑ k ∈ Finset.range (j+1), (j.choose k : ℝ)*M*C (j-k)*W^N := by
          apply Finset.sum_le_sum
          intro k hk
          have hk' : k ≤ j := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk
          have hV : ‖iteratedDeriv k spectralJLogPotential v‖ ≤ M := by
            rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
            exact hMb k hk' v hv
          have hG : ‖iteratedDeriv (j-k) g v‖ ≤ C (j-k)*W^N := by
            apply (hb (j-k) a u v ha hv).trans
            exact mul_le_mul_of_nonneg_left
              (pow_le_pow_right₀ hW (by dsimp [N]; omega)) (hC _).le
          simp only [norm_mul, norm_natCast]
          calc
            _ ≤ (j.choose k : ℝ)*M*(C (j-k)*W^N) :=
              mul_le_mul (mul_le_mul_of_nonneg_left hV (Nat.cast_nonneg _)) hG
                (norm_nonneg _) (by positivity)
            _ = _ := by ring
        _ = _ := by rw [← Finset.sum_mul]
    have ha₂ : ‖(a : ℂ)^2‖ ≤ R^2 := by
      rw [norm_pow, Complex.norm_real, Real.norm_eq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) ha 2
    rw [Function.iterate_succ_apply']
    change ‖iteratedDeriv j (spectralJLogSturm a g) v‖ ≤ _
    unfold spectralJLogSturm
    rw [iteratedDeriv_fun_add (hg''.of_le (by simp)).contDiffAt
      ((contDiff_const.mul hproduct).of_le (by simp)).contDiffAt,
      iteratedDeriv_const_mul_field]
    calc
      _ ≤ ‖iteratedDeriv j (deriv (deriv g)) v‖ +
          ‖(a : ℂ)^2*iteratedDeriv j (fun y => spectralJLogPotential y*g y) v‖ :=
        norm_add_le _ _
      _ ≤ C (j+2)*W^N + R^2*(S*W^N) := by
        rw [norm_mul]
        exact add_le_add hsecond (mul_le_mul ha₂ hprod (norm_nonneg _) (sq_nonneg R))
      _ ≤ _ := by
        change C (j+2)*W^N + R^2*(S*W^N) ≤ (C (j+2)+R^2*S+1)*W^N
        nlinarith [pow_nonneg (zero_le_one.trans hW) N]

end
end ArtinMatthews
