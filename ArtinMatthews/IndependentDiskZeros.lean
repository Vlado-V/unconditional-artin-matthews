module

public import Mathlib.Analysis.Complex.JensenFormula

/-! Finite disk zeros and their multiplicities, proved using the Mathlib
analytic divisor. The public statements match the character-disk inputs. -/

@[expose] public section

namespace Erdos970

open Filter Metric Set
open scoped BigOperators Topology

/-- The zeros of an analytic function in the specified closed disk. -/
def zerosetKfR (R : ℝ) (_hR : 0 < R) (f : ℂ → ℂ) : Set ℂ :=
  {z | z ∈ closedBall 0 R ∧ f z = 0}

private theorem diskOrder_ne_top {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) 1))
    {w z : ℂ} (hw : w ∈ closedBall (0 : ℂ) 1)
    (hz : z ∈ closedBall (0 : ℂ) 1) (hw0 : f w ≠ 0) :
    analyticOrderAt f z ≠ ⊤ := by
  apply AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected hf isPreconnected_closedBall hw hz
  rw [(hf w hw).analyticOrderAt_eq_zero.mpr hw0]
  exact WithTop.zero_ne_top

private theorem diskDivisor_eq {f : ℂ → ℂ} {R : ℝ} {z : ℂ}
    (hf : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) R))
    (hz : z ∈ closedBall (0 : ℂ) R) (hfin : analyticOrderAt f z ≠ ⊤) :
    MeromorphicOn.divisor f (closedBall (0 : ℂ) R) z =
      ((analyticOrderAt f z).toNat : ℤ) := by
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hf hz, ← ENat.natCast_toNat hfin]
  simp

theorem lem_Contra_finiteKR (R : ℝ) (hR : 0 < R) (hR' : R < 1)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) 1))
    (h_exists_nonzero : ∃ z ∈ ball (0 : ℂ) 1, f z ≠ 0) :
    (zerosetKfR R hR f).Finite := by
  obtain ⟨w, hw, hw0⟩ := h_exists_nonzero
  have hsub := closedBall_subset_closedBall (le_of_lt hR')
    (x := (0 : ℂ))
  have hfr := hf.mono hsub
  apply ((MeromorphicOn.divisor f (closedBall (0 : ℂ) R)).finiteSupport
    (isCompact_closedBall ..)).subset
  intro z hz
  have hn := diskOrder_ne_top hf (ball_subset_closedBall hw) (hsub hz.1) hw0
  have hp := ENat.toNat_pos ((hfr z hz.1).analyticOrderAt_ne_zero.mpr hz.2) hn
  change MeromorphicOn.divisor f (closedBall (0 : ℂ) R) z ≠ 0
  rw [diskDivisor_eq hfr hz.1 hn]
  exact_mod_cast hp.ne'

theorem lem_m_rho_is_nat (R R1 : ℝ) (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R)
    (f : ℂ → ℂ) (h_f_analytic : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) 1))
    (h_f_nonzero_at_zero : f 0 ≠ 0) (hR_lt_1 : R < 1) :
    ∀ z ∈ zerosetKfR R1 hR1_pos f, analyticOrderAt f z ≠ ⊤ := by
  intro z hz
  exact diskOrder_ne_top h_f_analytic (mem_closedBall_self zero_le_one)
    (closedBall_subset_closedBall (hR1_lt_R.trans hR_lt_1).le hz.1) h_f_nonzero_at_zero

theorem lem_m_rho_ge_1 (R R1 : ℝ) (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R)
    (f : ℂ → ℂ) (h_f_analytic : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) 1))
    (_h_f_nonzero_at_zero : f 0 ≠ 0) (hR_lt_1 : R < 1) :
    ∀ z ∈ zerosetKfR R1 hR1_pos f, analyticOrderAt f z ≥ 1 := by
  intro z hz
  have ha := h_f_analytic z (closedBall_subset_closedBall (hR1_lt_R.trans hR_lt_1).le hz.1)
  exact Order.one_le_iff_ne_zero.mpr (ha.analyticOrderAt_ne_zero.mpr hz.2)

theorem lem_analytic_zero_factor (R R1 : ℝ) (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ) (h_f_analytic : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) 1))
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (z : ℂ) (hz : z ∈ zerosetKfR R1 hR1_pos f) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g z ∧ g z ≠ 0 ∧
      ∀ᶠ w in 𝓝 z, f w = (w - z) ^ (analyticOrderAt f z).toNat * g w := by
  have ha := h_f_analytic z (closedBall_subset_closedBall (hR1_lt_R.trans hR_lt_1).le hz.1)
  have ht := lem_m_rho_is_nat R R1 hR1_pos hR1_lt_R f h_f_analytic
    h_f_nonzero_at_zero hR_lt_1 z hz
  obtain ⟨g, hg, hg0, heq⟩ := ha.analyticOrderAt_ne_top.mp ht
  refine ⟨g, hg, hg0, heq.mono ?_⟩
  intro w hw
  simpa only [smul_eq_mul, analyticOrderNatAt] using hw

theorem lem_sum_m_rho_bound (B R R1 : ℝ) (hB : 1 < B)
    (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
    (f : ℂ → ℂ) (h_f_analytic : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) 1))
    (h_f_nonzero_at_zero : f 0 ≠ 0) (hf0_eq_one : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 hR1_pos f).Finite)
    (h_σ : ℂ → (ℂ → ℂ)) (hf_le_B : ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ B)
    (_h_σ_spec : ∀ z ∈ zerosetKfR R1 hR1_pos f,
      AnalyticAt ℂ (h_σ z) z ∧ h_σ z z ≠ 0 ∧
      ∀ᶠ w in 𝓝 z, f w = (w - z) ^ (analyticOrderAt f z).toNat * h_σ z w) :
    (∑ z ∈ h_finite_zeros.toFinset, ((analyticOrderAt f z).toNat : ℝ)) ≤
      (1 / Real.log (R / R1)) * Real.log B := by
  have hR := hR1_pos.trans hR1_lt_R
  have hfR := h_f_analytic.mono (closedBall_subset_closedBall hR_lt_1.le)
  have hfR1 := hfR.mono (closedBall_subset_closedBall hR1_lt_R.le)
  let D := MeromorphicOn.divisor f (closedBall (0 : ℂ) R1)
  have hs : Function.support (⇑D) ⊆ ↑h_finite_zeros.toFinset := by
    intro z hz
    have hzb := D.supportWithinDomain hz
    refine h_finite_zeros.mem_toFinset.mpr ⟨hzb, ?_⟩
    by_contra hz0
    apply hz
    change D z = 0
    rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hfR1 hzb, (hfR1 z hzb).analyticOrderAt_eq_zero.mpr hz0]
    rfl
  have hJ := AnalyticOnNhd.sum_divisor_le (r := R1) (R := R) (M := B) (c := (0 : ℂ))
    (by simpa [abs_of_pos hR1_pos] using hR1_pos)
    (by simpa [abs_of_pos hR1_pos, abs_of_pos hR] using hR1_lt_R)
    hB.le (by simpa [abs_of_pos hR] using hfR) h_f_nonzero_at_zero
    (fun z hz => hf_le_B z
      (le_of_eq (by simpa [abs_of_pos hR] using hz)))
  rw [abs_of_pos hR1_pos, hf0_eq_one, norm_one, div_one] at hJ
  change (↑(∑ᶠ z, D z) : ℝ) ≤ _ at hJ
  rw [finsum_eq_sum_of_support_subset _ hs, Int.cast_sum] at hJ
  rw [one_div_mul_eq_div]
  convert hJ using 1
  refine Finset.sum_congr rfl fun z hz => ?_
  have hzero := h_finite_zeros.mem_toFinset.mp hz
  have hn := lem_m_rho_is_nat R R1 hR1_pos hR1_lt_R f h_f_analytic
    h_f_nonzero_at_zero hR_lt_1 z hzero
  rw [show D z = _ from diskDivisor_eq hfR1 hzero.1 hn]
  norm_cast

end Erdos970
