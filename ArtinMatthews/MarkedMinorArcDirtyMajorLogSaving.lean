module

public import ArtinMatthews.MarkedMinorArcDirtyMajorActualRow
public import ArtinMatthews.MarkedMinorArcDirtyMajorDecay


set_option backward.privateInPublic true
@[expose] public section

/-! Every logarithmic saving for the literal source-symmetrized weighted
major comparison row, with the actual logarithmic memory cutoff. -/
noncomputable section
namespace ArtinMatthews

open Filter
open scoped BigOperators Topology

theorem markedDirtyMajorActualConstant_nonneg (groups : ℕ) {v₀ H W c Bτ K : ℝ}
    (hv₀ : 1 ≤ v₀) (hW : 0 ≤ W) :
    0 ≤ markedDirtyMajorActualConstant groups v₀ H W c Bτ K := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold markedDirtyMajorActualConstant
  positivity

theorem markedDirtyMajorEnvelope_eventually_le {C : ℝ} (hC : 0 ≤ C)
    (groups : ℕ) (A₀ A : ℝ) :
    ∀ᶠ x : ℝ in atTop, markedDirtyMajorEnvelope C groups A₀ x ≤ (Real.log x)^(-A) := by
  have ht := markedDirtyMajorEnvelope_log_tendsto hC groups A₀ A
  filter_upwards [ht.eventually (gt_mem_nhds (show (0:ℝ)<1 by norm_num)),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with x hx hlog
  have hL : 0 < Real.log x := by linarith
  have hp : 0 < (Real.log x)^A := Real.rpow_pos_of_pos hL _
  have hh : markedDirtyMajorEnvelope C groups A₀ x ≤ 1/((Real.log x)^A) :=
    (le_div_iff₀ hp).mpr (by simpa only [mul_comm] using hx.le)
  simpa only [Real.rpow_neg hL.le,one_div] using hh

set_option backward.isDefEq.respectTransparency false in
theorem markedDirtyMajor_actual_weighted_row_log_saving {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j, (1/10:ℝ) ≤ e j) (I : Finset J) (jstar : I)
    (η ψ : ℝ → ℂ) (v₀ c Bτ K H W A₀ A : ℝ)
    (hv₀ : 1 ≤ v₀) (hc : 0 < c) (hBτ : 0 ≤ Bτ) (hH : 0 ≤ H) (hW : 0 ≤ W)
    (hη : ∀ t, ‖η t‖ ≤ H) (hψ : ∀ t, ‖ψ t‖ ≤ W)
    (hsupp : Function.support ψ ⊆ Set.Icc (-K) K) :
    ∀ᶠ x : ℝ in atTop, ∀ (pads : ℕ) (Z : Finset (ℤ × ℤ))
      (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (r d₀ Y q ρ : ℝ)
      (w : Z → ℤ × ℤ)
      (χ : MarkedRawState (markedRawActualPrimeBand e x) (pads+1) (markedDirtyMemoryCutoff x) Z → ℂ)
      (s : MarkedRawState (markedRawActualPrimeBand e x) (pads+1) (markedDirtyMemoryCutoff x) Z),
      Real.exp ((Real.log x)^(1/10:ℝ)) ≤ Y → 0 ≤ q → q ≤ 1 → 0 ≤ ρ → ρ ≤ 1 →
      (∀ z, markedMinorIntegerDet z.1 (w z)=1) →
      (∀ z ∈ Z, c ≤ |markedMinorIntegerTau r z| ∧ |markedMinorIntegerTau r z| ≤ Bτ) →
      (∀ s, ‖χ s‖ ≤ 1) →
      markedDirtyMajorSymWeightedRow (markedRawActualPrimeAtom e q x)
        (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) hZ η ψ r d₀ Y
        ((Real.log x)^A₀) ρ v₀ w χ s I ≤ (Real.log x)^(-A) := by
  let C := markedDirtyMajorActualConstant (Fintype.card J) v₀ H W c Bτ K
  have hC : 0 ≤ C := markedDirtyMajorActualConstant_nonneg _ hv₀ hW
  filter_upwards [markedDirtyMajor_actual_weighted_row_eventually e he I jstar,
    markedDirtyMajorEnvelope_eventually_le (mul_nonneg (by norm_num : (0:ℝ)≤2) hC)
      (Fintype.card J) A₀ A,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with x hx henv hlog
  intro pads Z hZ r d₀ Y q ρ w χ s hYexp hq₀ hq₁ hρ₀ hρ₁ hw hτ hχ
  have hL : 0 < Real.log x := by linarith
  have hY : 1 ≤ Y := (show 1 ≤ Real.exp ((Real.log x)^(1/10:ℝ)) by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (Real.rpow_nonneg hL.le (1/10:ℝ))).trans hYexp
  have hrow := hx pads (markedDirtyMemoryCutoff x) Z hZ η ψ r d₀ Y ((Real.log x)^A₀) q ρ v₀ c Bτ K H W
    w χ s hY (Real.rpow_nonneg hL.le _) hq₀ hq₁ hc hBτ hρ₀ hρ₁ hv₀ hH hW hη hψ hsupp hw hτ hχ
  apply hrow.trans
  apply le_trans ?_ henv
  calc
    _ ≤ C*(markedDirtyMemoryCutoff x+1:ℝ)^(Fintype.card J)*((Real.log x)^A₀)^3*
        (2*Real.exp (-(1/10:ℝ)*(Real.log x)^(1/10:ℝ))) := by
      exact mul_le_mul_of_nonneg_left (markedDirtyMajor_tail_le hL.le hYexp) (by positivity)
    _ = markedDirtyMajorEnvelope (2*C) (Fintype.card J) A₀ x := by
      unfold markedDirtyMajorEnvelope
      ring

end ArtinMatthews
