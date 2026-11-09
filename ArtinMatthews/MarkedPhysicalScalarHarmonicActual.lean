module

public import ArtinMatthews.MarkedPhysicalScalarPairingActual
public import ArtinMatthews.MarkedPhysicalTypeIIDyadSaving


set_option backward.privateInPublic true
@[expose] public section

/-! The arbitrary-coefficient estimate on the actual harmonic-padded source. -/
namespace ArtinMatthews
open Filter
open scoped BigOperators Classical
noncomputable section

/-- The genuine reciprocal dyad weight and primitive boxes remain in the
harmonic sums. The actual dyad count absorbs their fixed logarithmic loss. -/
theorem markedPhysicalScalarHarmonic_actual_log_saving
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j) (heUpper : ∀ j,e j ≤ (1/5:ℝ))
    (hinj : Function.Injective e) {δ : ℝ} (hδ : 0 < δ)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (K B W Cα Cβ P : ℝ) (hK : 0 ≤ K) (hB : 8 ≤ B) (hW : 0 ≤ W)
    (hCα : 0 ≤ Cα) (hCβ : 0 ≤ Cβ) (hP : 0 ≤ P)
    (hdepth : 100*(5*(P+2*(Cα+Cβ)+5)+36)<(Fintype.card J:ℝ))
    (hηsupport : Function.support η ⊆ Set.Icc 1 4) (hη : ∀ t,‖η t‖ ≤ 1)
    (hψ : ∀ t,‖ψ t‖ ≤ W) (hψsupport : Function.support ψ ⊆ Set.Icc (-K) K) :
    ∀ᶠ x : ℝ in atTop,∀ (Y Hm Hn : ℝ),
      Real.exp ((Real.log x)^(1/10:ℝ)) ≤ Y → Y ≤ Real.exp (B*(Real.log x)^(1/5:ℝ)) →
      x^δ ≤ Hm → x^δ ≤ Hn → ∀ α β : ℕ → ℂ,
      (∀ n,‖α n‖ ≤ (Real.log x)^Cα) → (∀ n,‖β n‖ ≤ (Real.log x)^Cβ) →
      let bands := fun j => markedLogPowerBand (e j) x
      let pads := ⌊(Real.log x)^(1/100:ℝ)⌋₊
      let Q := (Real.log x)^(P+2*(Cα+Cβ)+14)
      let Z := markedPhysicalTypeIIDyadBox Y Hm Hn
      ‖markedPhysicalHarmonicPaddedDetectorSum bands pads Z η Y (markedRawEdgeDeltaDetector ψ Y) α β-
        markedPhysicalHarmonicPaddedDetectorSum bands pads Z η Y (markedRawEdgeMajorDetector ψ Q Y) α β‖ ≤
        (Y*(Hm*Hn))*(Real.log x)^(-P) := by
  have hB₀ : 0 ≤ B := by linarith
  have hE : 0 ≤ 2*(Fintype.card J:ℝ)+B := by positivity
  have hdep : 100*(5*((P+2)+2*(Cα+Cβ)+3)+36)<(Fintype.card J:ℝ) := by linarith
  have hQ : (P+2)+2*(Cα+Cβ)+12=P+2*(Cα+Cβ)+14 := by ring
  filter_upwards [markedPhysicalScalarPairing_actual_log_saving e he heUpper hinj hδ ψ η
      K (2*(Fintype.card J:ℝ)+B) B W Cα Cβ (P+2) hK hE hB hW hCα hCβ (by linarith) hdep
      hηsupport hη hψ hψsupport,
    markedPhysicalActualPadDyad_sum_log_saving e heUpper P,eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with x hphys hsum hx hlog
  intro Y Hm Hn hY hYhi hHm hHn α β hα hβ
  dsimp only
  let L := Real.log x
  let bands := fun j => markedLogPowerBand (e j) x
  let pads := ⌊L^(1/100:ℝ)⌋₊
  let Q := L^(P+2*(Cα+Cβ)+14)
  let Z := markedPhysicalTypeIIDyadBox Y Hm Hn
  let f (j : ℕ) := markedPhysicalScalarPairing e x ψ η ((2:ℕ)^j) Y Q 1
    (((2:ℕ)^j:ℝ)*Y*Hm) Hn α β
  have hYp : 0 < Y := (Real.exp_pos _).trans_le hY
  have hY1 : 1 ≤ Y := (Real.one_le_exp (Real.rpow_nonneg (zero_le_one.trans hlog) _)).trans hY
  have hmp : 0 < Hm := (Real.rpow_pos_of_pos (zero_lt_one.trans hx) δ).trans_le hHm
  have hnp : 0 < Hn := (Real.rpow_pos_of_pos (zero_lt_one.trans hx) δ).trans_le hHn
  have hsum' := hsum (Y*(Hm*Hn)) (by positivity) f (fun j hj => by
    let d := ((2:ℕ)^j:ℝ)
    have hd : 1 ≤ d := (markedPhysicalActualPadDyad_scale e hlog heUpper j hj).1
    have hU : x^δ ≤ d*Y*Hm := hHm.trans
      (le_mul_of_one_le_left hmp.le (one_le_mul_of_one_le_of_one_le hd hY1))
    have hs := markedPhysicalActualPadDyad_Y_bound e hlog heUpper B Y hB₀ hYp.le hYhi j hj
    have hp := hphys d Y (zero_lt_one.trans_le hd) hY hYhi hs (d*Y*Hm) Hn hU hHn α β hα hβ
    rw [hQ] at hp
    exact hp.trans_eq (by ring))
  have heq : (∑ j∈markedPhysicalPadDyadIndices bands pads, (((2:ℕ)^j:ℝ):ℂ)⁻¹*f j) =
      markedPhysicalHarmonicPaddedDetectorSum bands pads Z η Y (markedRawEdgeDeltaDetector ψ Y) α β-
        markedPhysicalHarmonicPaddedDetectorSum bands pads Z η Y (markedRawEdgeMajorDetector ψ Q Y) α β :=
    markedPhysicalEdgePairing_dyad_delta_sub_major bands (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1)
      pads Z (fun _ _ hz => (Finset.mem_filter.mp hz).2) ψ η Y Q 1 α β
  exact (congrArg norm heq).symm.le.trans hsum'

end
end ArtinMatthews
