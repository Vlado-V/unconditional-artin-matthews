module

public import ArtinMatthews.SourceMellinLogPullbackCalculus
public import Mathlib.Topology.Order.Bornology
public import Mathlib.Tactic.Ring


set_option backward.privateInPublic true
@[expose] public section

/-! Higher derivative energy of the compact logarithmic pullback, with
the additive energies localized to the fixed positive interval. -/
namespace ArtinMatthews

open MeasureTheory Set
open scoped ContDiff SchwartzMap BigOperators

noncomputable section

private def expCutoff (χ : ℝ → ℂ) : ℝ → ℂ :=
  χ * (fun u => (Real.exp u : ℂ))

private theorem expCutoff_contDiff (χ : ℝ → ℂ) (hχ : ContDiff ℝ ∞ χ) :
    ContDiff ℝ ∞ (expCutoff χ) := by
  change ContDiff ℝ ∞ (χ * (Complex.ofRealCLM ∘ Real.exp))
  exact hχ.mul (Complex.ofRealCLM.contDiff.comp Real.contDiff_exp)

private theorem logPullback_energy_succ
    (χ : ℝ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (g : 𝓢(ℝ, ℂ)) (k : ℕ) :
    (∫ u, ‖iteratedDeriv (k+1) (sourceMellinLogPullback χ g) u‖ ^ 2) ≤
      2 * (∫ u, ‖iteratedDeriv k (sourceMellinLogPullback (deriv χ) g) u‖ ^ 2) +
        2 * (∫ u, ‖iteratedDeriv k
          (sourceMellinLogPullback (expCutoff χ) (SchwartzMap.derivCLM ℂ ℂ g)) u‖ ^ 2) := by
  let g' := SchwartzMap.derivCLM ℂ ℂ g
  let f := sourceMellinLogPullback (deriv χ) g
  let h := sourceMellinLogPullback (expCutoff χ) g'
  have hχ₀ : ContDiff ℝ ∞ (deriv χ) := (contDiff_infty_iff_deriv.mp hχ).2
  have hχ₁ : ContDiff ℝ ∞ (expCutoff χ) := expCutoff_contDiff χ hχ
  have hc₁ : HasCompactSupport (expCutoff χ) := hc.mul_right
  have hf := sourceMellinLogPullback_contDiff (deriv χ) hχ₀ g
  have hh := sourceMellinLogPullback_contDiff (expCutoff χ) hχ₁ g'
  have hfi := sourceMellinLogPullback_derivative_integrable_sq (deriv χ) hχ₀ hc.deriv g k
  have hhi := sourceMellinLogPullback_derivative_integrable_sq (expCutoff χ) hχ₁ hc₁ g' k
  have hGi := sourceMellinLogPullback_derivative_integrable_sq χ hχ hc g (k+1)
  have he : deriv (sourceMellinLogPullback χ g) = f + h := sourceMellinLogPullback_deriv χ hχ g
  have hp (u : ℝ) :
      ‖iteratedDeriv (k+1) (sourceMellinLogPullback χ g) u‖ ^ 2 ≤
        2 * ‖iteratedDeriv k f u‖ ^ 2 + 2 * ‖iteratedDeriv k h u‖ ^ 2 := by
    rw [iteratedDeriv_succ', he, iteratedDeriv_add
      (hf.contDiffAt.of_le (by simp)) (hh.contDiffAt.of_le (by simp))]
    let a := iteratedDeriv k f u
    let b := iteratedDeriv k h u
    have hs : ‖a+b‖ ^ 2 ≤ (‖a‖+‖b‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_add_le a b) 2
    change ‖a+b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2
    nlinarith [sq_nonneg (‖a‖-‖b‖)]
  calc
    _ ≤ ∫ u, 2 * ‖iteratedDeriv k f u‖ ^ 2 + 2 * ‖iteratedDeriv k h u‖ ^ 2 :=
      integral_mono hGi ((hfi.const_mul 2).add (hhi.const_mul 2)) hp
    _ = _ := by
      rw [integral_add (hfi.const_mul 2) (hhi.const_mul 2), integral_const_mul, integral_const_mul]

theorem sourceMellinLogPullback_derivative_energy_local
    (χ : ℝ → ℂ) (hχ : ContDiff ℝ ∞ χ) {a b : ℝ} (hs : tsupport χ ⊆ Icc a b) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : 𝓢(ℝ, ℂ),
      (∫ u, ‖iteratedDeriv k (sourceMellinLogPullback χ g) u‖ ^ 2) ≤
        C * ∑ ℓ ∈ Finset.range (k+1),
          ∫ x in Icc (Real.exp a) (Real.exp b), ‖iteratedDeriv ℓ (g : ℝ → ℂ) x‖ ^ 2 := by
  induction k generalizing χ with
  | zero =>
    obtain ⟨C,hC,h⟩ := sourceMellinLogPullback_zero_energy_on χ hχ.continuous hs
    refine ⟨C,hC,fun g => ?_⟩
    simpa only [iteratedDeriv_zero, Nat.zero_add, Finset.sum_range_one] using h g
  | succ k ih =>
    have hc : HasCompactSupport χ := isCompact_Icc.of_isClosed_subset isClosed_closure hs
    have hχ₀ : ContDiff ℝ ∞ (deriv χ) := (contDiff_infty_iff_deriv.mp hχ).2
    have hχ₁ : ContDiff ℝ ∞ (expCutoff χ) := expCutoff_contDiff χ hχ
    have hs₀ : tsupport (deriv χ) ⊆ Icc a b := tsupport_deriv_subset.trans hs
    have hs₁ : tsupport (expCutoff χ) ⊆ Icc a b := tsupport_mul_subset_left.trans hs
    obtain ⟨C₀,hC₀,h₀⟩ := ih (deriv χ) hχ₀ hs₀
    obtain ⟨C₁,hC₁,h₁⟩ := ih (expCutoff χ) hχ₁ hs₁
    refine ⟨2*(C₀+C₁),by positivity,fun g => ?_⟩
    let g' := SchwartzMap.derivCLM ℂ ℂ g
    let A (j : ℕ) := ∫ x in Icc (Real.exp a) (Real.exp b), ‖iteratedDeriv j (g : ℝ → ℂ) x‖ ^ 2
    let E := ∑ j ∈ Finset.range (k+1+1), A j
    have hA (j : ℕ) : 0 ≤ A j := integral_nonneg fun _ => sq_nonneg _
    have hsum₀ : (∑ j ∈ Finset.range (k+1), A j) ≤ E := by
      change _ ≤ ∑ j ∈ Finset.range (k+1+1), A j
      rw [Finset.sum_range_succ A (k+1)]
      exact le_add_of_nonneg_right (hA (k+1))
    have hsum₁ : (∑ j ∈ Finset.range (k+1), A (j+1)) ≤ E := by
      change _ ≤ ∑ j ∈ Finset.range (k+1+1), A j
      rw [Finset.sum_range_succ' A (k+1)]
      exact le_add_of_nonneg_right (hA 0)
    have h₀' : (∫ u, ‖iteratedDeriv k (sourceMellinLogPullback (deriv χ) g) u‖ ^ 2) ≤
        C₀ * ∑ j ∈ Finset.range (k+1), A j := h₀ g
    have hg' : (g' : ℝ → ℂ) = deriv g := rfl
    have h₁' : (∫ u, ‖iteratedDeriv k (sourceMellinLogPullback (expCutoff χ) g') u‖ ^ 2) ≤
        C₁ * ∑ j ∈ Finset.range (k+1), A (j+1) := by
      simpa only [A,hg',iteratedDeriv_succ'] using h₁ g'
    have h0E := h₀'.trans (mul_le_mul_of_nonneg_left hsum₀ hC₀)
    have h1E := h₁'.trans (mul_le_mul_of_nonneg_left hsum₁ hC₁)
    change (∫ u, ‖iteratedDeriv (k+1) (sourceMellinLogPullback χ g) u‖ ^ 2) ≤ 2*(C₀+C₁)*E
    calc
      _ ≤ 2*(∫ u, ‖iteratedDeriv k (sourceMellinLogPullback (deriv χ) g) u‖ ^ 2) +
          2*(∫ u, ‖iteratedDeriv k (sourceMellinLogPullback (expCutoff χ) g') u‖ ^ 2) :=
        logPullback_energy_succ χ hχ hc g k
      _ ≤ 2*(C₀*E) + 2*(C₁*E) := by gcongr
      _ = _ := by ring

private theorem schwartz_iteratedDeriv_integrable_sq (k : ℕ) (g : 𝓢(ℝ, ℂ)) :
    Integrable (fun x => ‖iteratedDeriv k (g : ℝ → ℂ) x‖ ^ 2) := by
  induction k generalizing g with
  | zero =>
    simpa only [iteratedDeriv_zero] using (g.memLp 2).integrable_norm_pow (p := 2) (by decide)
  | succ k ih =>
    rw [iteratedDeriv_succ']
    exact ih (SchwartzMap.derivCLM ℂ ℂ g)

theorem sourceMellinLogPullback_derivative_energy
    (χ : ℝ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : 𝓢(ℝ, ℂ)) (R E : ℝ), 1 ≤ R → 0 ≤ E →
      (∀ ℓ ≤ k, (∫ x, ‖iteratedDeriv ℓ (g : ℝ → ℂ) x‖ ^ 2) ≤ R^(2*ℓ)*E) →
      (∫ u, ‖iteratedDeriv k (fun u => χ u * g (Real.exp u)) u‖ ^ 2) ≤ C*R^(2*k)*E := by
  let a := sInf (tsupport χ)
  let b := sSup (tsupport χ)
  have hs : tsupport χ ⊆ Icc a b :=
    (show IsCompact (tsupport χ) from hc).isBounded.subset_Icc_sInf_sSup
  obtain ⟨C,hC,h⟩ := sourceMellinLogPullback_derivative_energy_local χ hχ hs k
  refine ⟨C*((k+1:ℕ):ℝ),by positivity,fun g R E hR hE hDer => ?_⟩
  let A (j : ℕ) := ∫ x in Icc (Real.exp a) (Real.exp b), ‖iteratedDeriv j (g : ℝ → ℂ) x‖ ^ 2
  have hA (j : ℕ) (hj : j ∈ Finset.range (k+1)) : A j ≤ R^(2*k)*E := by
    have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    calc
      A j ≤ ∫ x, ‖iteratedDeriv j (g : ℝ → ℂ) x‖ ^ 2 :=
        integral_mono_measure Measure.restrict_le_self
          (ae_of_all _ fun _ => sq_nonneg _) (schwartz_iteratedDeriv_integrable_sq j g)
      _ ≤ R^(2*j)*E := hDer j hjk
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hR (Nat.mul_le_mul_left 2 hjk)) hE
  calc
    _ ≤ C * ∑ j ∈ Finset.range (k+1), A j := h g
    _ ≤ C * ∑ j ∈ Finset.range (k+1), R^(2*k)*E :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hA) hC
    _ = _ := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring

end
end ArtinMatthews
