module

public import ArtinMatthews.MarkedPhysicalRootDiscrepancyMass
public import ArtinMatthews.MarkedPhysicalGlobalRootReplacement


set_option backward.privateInPublic true
@[expose] public section

/-! The actual absolute root-error mass saves every growing-moment
logarithmic power, uniformly through the odd Bonferroni level. All
selected residue classes, physical mass and source radius are counted. -/

namespace ArtinMatthews
open Filter
open scoped BigOperators Classical
noncomputable section

theorem markedPhysicalCoordinateDiscrepancyMass_moment_log_saving
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j) (heUpper : ∀ j,e j ≤ (1/5:ℝ))
    {δ : ℝ} (hδ : 0 < δ)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (K Hexp B etaBound psiBound Qexp G : ℝ)
    (hK : 0 ≤ K) (hHexp : 0 ≤ Hexp) (hB : 8 ≤ B)
    (heta : 0 ≤ etaBound) (hpsi : 0 ≤ psiBound) (hQexp : 0 ≤ Qexp) (hG : 0 ≤ G)
    (hη : ∀ t,‖η t‖ ≤ etaBound) (hψ : ∀ t,‖ψ t‖ ≤ psiBound) :
    ∀ᶠ x : ℝ in atTop,∀ (d₀ Y : ℝ) (hd₀ : 0 ≤ d₀)
      (hY : Real.exp ((Real.log x)^(1/10:ℝ)) ≤ Y), Y ≤ Real.exp (B*(Real.log x)^(1/5:ℝ)) →
      d₀*Y ≤ Real.exp (Hexp*(Real.log x)^(21/100:ℝ)) →
      ∀ (q U Vr : ℝ),0 ≤ q → q ≤ 1 → x^δ ≤ U → x^δ ≤ Vr →
      let _R := markedPhysicalMomentTubeRadius (markedMemoryMomentLength x) K (d₀*Y)
      let hR := markedPhysicalMomentTubeRadius_ge_one (markedMemoryMomentLength x) hK
        (mul_nonneg hd₀ ((Real.exp_pos _).le.trans hY))
      ∀ k : ℕ,k ≤ 2*markedPhysicalBonferroniDepth x+1 →
      markedPhysicalCoordinateDiscrepancyMass e x ψ η d₀ Y ((Real.log x)^Qexp) hR q U Vr k /
        (U*Vr) ≤ (Real.log x)^(-G*(markedMemoryMomentLength x:ℝ)) := by
  let C := markedPhysicalGlobalResidueCost (Fintype.card J) K Hexp
  let B₁ := max B (43+1024*K+Hexp)
  have hB₁ : 8 ≤ B₁ := hB.trans (le_max_left _ _)
  have he0 : ∀ j,0 < e j := fun j => lt_of_lt_of_le (by norm_num) (he j)
  have hmass := markedPhysicalGlobalSelectedResidue_mass_bound e he0 heUpper
  have hroot := markedPhysicalCoordinateIndex_selected_root_log_saving e he heUpper hδ
    B₁ C G Qexp hB₁ hG hQexp ψ η etaBound psiBound (Real.log 2/2)
    heta hpsi (by positivity) hη hψ
  have hbands := eventually_all.mpr (fun j => marked_log_power_band_mass_eventually (he0 j))
  filter_upwards [hroot,hmass,hbands,eventually_gt_atTop (0:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with x hx hm hb hx0 hlog
  intro d₀ Y hd₀ hY hYhi hscale q U Vr hq0 hq1 hU hVr
  dsimp only
  intro k hk
  let R := markedPhysicalMomentTubeRadius (markedMemoryMomentLength x) K (d₀*Y)
  have hY0 : 0 ≤ Y := (Real.exp_pos _).le.trans hY
  have hH : 0 ≤ d₀*Y := mul_nonneg hd₀ hY0
  have hR : 1 ≤ R := markedPhysicalMomentTubeRadius_ge_one _ hK hH
  have huv : 0 < U*Vr := mul_pos
    ((Real.rpow_pos_of_pos hx0 δ).trans_le hU) ((Real.rpow_pos_of_pos hx0 δ).trans_le hVr)
  have hRhi : (R:ℝ)+1 ≤ Real.exp (B₁*(Real.log x)^(99/100:ℝ)) := by
    have hw := markedPhysicalMomentTube_width_sharp hlog hK hH hHexp hscale
    calc
      _ ≤ 2*(R:ℝ)+1 := by linarith [Nat.cast_nonneg R (α := ℝ)]
      _ ≤ Real.exp ((43+1024*K+Hexp)*(Real.log x)^(23/100:ℝ)) := hw
      _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul
        (le_max_right B _) (Real.rpow_le_rpow_of_exponent_le hlog (by norm_num))
        (Real.rpow_nonneg (zero_le_one.trans hlog) _)
        (show 0 ≤ B₁ from (by norm_num : (0:ℝ) ≤ 8).trans hB₁))
  have hYhi₁ : Y ≤ Real.exp (B₁*(Real.log x)^(1/5:ℝ)) :=
    hYhi.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg (zero_le_one.trans hlog) _)))
  have hQ : 1 ≤ (Real.log x)^Qexp := Real.one_le_rpow hlog hQexp
  let E := Real.exp (C*(Real.log x)^(99/100:ℝ))
  let P := (Real.log x)^(-G*(markedMemoryMomentLength x:ℝ))
  let ε := U*Vr*(P/E)
  have hE : 0 < E := Real.exp_pos _
  have hP : 0 ≤ P := Real.rpow_nonneg (zero_le_one.trans hlog) _
  have hε : 0 ≤ ε := mul_nonneg huv.le (div_nonneg hP hE.le)
  have heach (i : MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x)
      (markedPadSlots x) (markedMemoryMomentLength x) R) (T : Finset ℕ)
      (hT : T ⊆ markedPhysicalBandPrimes (fun j => markedLogPowerBand (e j) x) \
        markedPhysicalPathUsedPrimes Finset.univ i.1) (hc : T.card ≤ k) :
      ‖markedPhysicalCoordinateSelectedRoot e x
          (fun j => bandReciprocalMass (markedLogPowerBand (e j) x))
          ψ η d₀ Y ((Real.log x)^Qexp) i hR q U Vr T-
        markedPhysicalCoordinateSelectedAverage e x
          (fun j => bandReciprocalMass (markedLogPowerBand (e j) x))
          ψ η d₀ Y ((Real.log x)^Qexp) i hR q U Vr T‖ ≤
        (Nat.card (Matrix.SpecialLinearGroup (Fin 2)
          (ZMod (markedPhysicalBonferroniModulus Finset.univ i.1 T))):ℝ)*ε := by
    let hTP : T ⊆ markedPhysicalBandPrimes (fun j => markedLogPowerBand (e j) x) :=
      fun _ hp => (Finset.mem_sdiff.mp (hT hp)).1
    apply markedPhysicalCoordinateSelectedRoot_error e x _ ψ η d₀ Y ((Real.log x)^Qexp)
      i hR q U Vr ε T hTP
    intro g
    have hr := hx (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) R i hR T hT
      (hc.trans hk) g U Vr d₀ Y ((Real.log x)^Qexp) q
      (fun j => (hb j).1.le) hU hVr hY hYhi₁ hRhi hQ le_rfl hq0 hq1
    dsimp only at hr
    change E * _ ≤ P at hr
    rw [mul_comm E] at hr
    have hdiv := (le_div_iff₀ hE).mpr hr
    have hn := (div_le_iff₀ huv).mp hdiv
    simpa only [ε,mul_comm] using hn
  have herr := markedPhysicalCoordinateDiscrepancyMass_le e x ψ η d₀ Y ((Real.log x)^Qexp)
    hR q U Vr ε hε k (2*markedPhysicalBonferroniDepth x+1) hk heach
  have htotal : markedPhysicalMass
      (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) (markedPadSlots x)*
      (∑ i : MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x)
        (markedPadSlots x) (markedMemoryMomentLength x) R,
        markedPhysicalSelectedResidueCount e x i.1 (2*markedPhysicalBonferroniDepth x+1)) ≤ E :=
    hm K (d₀*Y) Hexp hK hH hHexp hscale
  apply (div_le_iff₀ huv).mpr
  calc
    _ ≤ _ := herr
    _ ≤ E*ε := mul_le_mul_of_nonneg_right htotal hε
    _ = P*(U*Vr) := by dsimp [ε]; field_simp [hE.ne']

theorem markedPhysicalOddRootDiscrepancyMass_moment_log_saving
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j) (heUpper : ∀ j,e j ≤ (1/5:ℝ))
    {δ : ℝ} (hδ : 0 < δ)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (K Hexp B etaBound psiBound Qexp G : ℝ)
    (hK : 0 ≤ K) (hHexp : 0 ≤ Hexp) (hB : 8 ≤ B)
    (heta : 0 ≤ etaBound) (hpsi : 0 ≤ psiBound) (hQexp : 0 ≤ Qexp) (hG : 0 ≤ G)
    (hη : ∀ t,‖η t‖ ≤ etaBound) (hψ : ∀ t,‖ψ t‖ ≤ psiBound) :
    ∀ᶠ x : ℝ in atTop,∀ (d₀ Y : ℝ) (hd₀ : 0 ≤ d₀)
      (hY : Real.exp ((Real.log x)^(1/10:ℝ)) ≤ Y), Y ≤ Real.exp (B*(Real.log x)^(1/5:ℝ)) →
      d₀*Y ≤ Real.exp (Hexp*(Real.log x)^(21/100:ℝ)) →
      ∀ (q U Vr : ℝ),0 ≤ q → q ≤ 1 → x^δ ≤ U → x^δ ≤ Vr →
      let _R := markedPhysicalMomentTubeRadius (markedMemoryMomentLength x) K (d₀*Y)
      let hR := markedPhysicalMomentTubeRadius_ge_one (markedMemoryMomentLength x) hK
        (mul_nonneg hd₀ ((Real.exp_pos _).le.trans hY))
      markedPhysicalOddRootDiscrepancyMass e x ψ η d₀ Y ((Real.log x)^Qexp) hR q U Vr /
        (U*Vr) ≤ (Real.log x)^(-G*(markedMemoryMomentLength x:ℝ)) := by
  filter_upwards [markedPhysicalCoordinateDiscrepancyMass_moment_log_saving e he heUpper hδ
    ψ η K Hexp B etaBound psiBound Qexp G hK hHexp hB heta hpsi hQexp hG hη hψ] with x hx
  intro d₀ Y hd₀ hY hYhi hscale q U Vr hq0 hq1 hU hVr
  exact hx d₀ Y hd₀ hY hYhi hscale q U Vr hq0 hq1 hU hVr _ le_rfl

end
end ArtinMatthews
