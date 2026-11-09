module

public import ArtinMatthews.MarkedPhysicalSourceGlobalSaving
public import ArtinMatthews.MarkedPhysicalSourceMomentIdentity


set_option backward.privateInPublic true
@[expose] public section

/-! The literal original physical matrix moment is approximated by
the actual capped line main term, with its root density explicit. -/
namespace ArtinMatthews
open Filter
open scoped BigOperators Classical
noncomputable section
attribute [local instance] markedPhysicalMomentFintype markedPhysicalMomentDecidableEq

theorem markedPhysicalPositionMoment_capped_moment_log_saving
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j) (heUpper : ∀ j,e j ≤ (1/5:ℝ))
    (hinj : Function.Injective e) {δ : ℝ} (hδ : 0 < δ)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (K Hexp B etaBound psiBound Qexp G : ℝ)
    (hK : 0 ≤ K) (hHexp : 0 ≤ Hexp) (hB : 8 ≤ B)
    (heta : 0 ≤ etaBound) (hpsi : 0 ≤ psiBound) (hQexp : 0 ≤ Qexp) (hG : 0 ≤ G)
    (hη : ∀ t,‖η t‖ ≤ etaBound) (hψ : ∀ t,‖ψ t‖ ≤ psiBound)
    (hψsupport : Function.support ψ ⊆ Set.Icc (-K) K) :
    ∀ᶠ x : ℝ in atTop,∀ (d₀ Y : ℝ) (hd₀ : 0 < d₀)
      (hY : Real.exp ((Real.log x)^(1/10:ℝ)) ≤ Y), Y ≤ Real.exp (B*(Real.log x)^(1/5:ℝ)) →
      d₀*Y ≤ Real.exp (Hexp*(Real.log x)^(21/100:ℝ)) →
      ∀ (q U Vr : ℝ),0 ≤ q → q ≤ 1 → x^δ ≤ U → x^δ ≤ Vr →
      let R := markedPhysicalMomentTubeRadius (markedMemoryMomentLength x) K (d₀*Y)
      let hR := markedPhysicalMomentTubeRadius_ge_one (markedMemoryMomentLength x) hK
        (mul_nonneg hd₀.le ((Real.exp_pos _).le.trans hY))
      ∀ (w : ↥(markedPhysicalPrimitiveBox U (16*U) Vr (2*Vr)) → ℤ × ℤ),
      (∀ a,markedMinorIntegerDet a.1 (w a)=1) →
      |markedPhysicalPositionMoment (fun j => markedLogPowerBand (e j) x) (markedPadSlots x)
          (markedPhysicalPrimitiveBox U (16*U) Vr (2*Vr))
          (fun j => bandReciprocalMass (markedLogPowerBand (e j) x))
          (markedPhysicalRestrictedMatrix (fun j => markedLogPowerBand (e j) x)
            (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1)
            (fun j => bandReciprocalMass (markedLogPowerBand (e j) x))
            ⌊(Real.log x)^(1/100:ℝ)⌋₊ (markedPhysicalPrimitiveBox U (16*U) Vr (2*Vr))
            (fun _ hz => (Finset.mem_filter.mp hz).2) ψ η d₀ Y ((Real.log x)^Qexp) q
            (MarkedPhysicalActualGood e x d₀ Y w)) ⌈(Real.log x)^(1/2:ℝ)/2⌉₊-
        (U*Vr/(riemannZeta 2).re)*
          (markedPhysicalCoordinateCappedGlobal e x ψ η d₀ Y ((Real.log x)^Qexp) q U Vr R hR).re| /
          (U*Vr) ≤ (Real.log x)^(-G*(markedMemoryMomentLength x:ℝ)) := by
  have he0 : ∀ j,0 < e j := fun j => lt_of_lt_of_le (by norm_num) (he j)
  have hbands := eventually_all.mpr (fun j => marked_log_power_band_mass_eventually (he0 j))
  filter_upwards [markedPhysicalSourceDampingGlobal_capped_moment_log_saving e he heUpper hinj hδ
    ψ η K Hexp B etaBound psiBound Qexp G hK hHexp hB heta hpsi hQexp hG hη hψ,
    marked_array_disjoint_eventually e hinj,hbands,eventually_gt_atTop (1:ℝ)] with x hs hdis hb hx
  intro d₀ Y hd₀ hY hYhi hscale q U Vr hq0 hq1 hU hVr
  dsimp only
  intro w hw
  let S : MarkedPhysicalLabelPath (fun j => markedLogPowerBand (e j) x)
      (markedPadSlots x) (markedMemoryMomentLength x) → ℕ := fun _ => 1
  have hS : ∀ a,S a≠0 := fun _ => by norm_num [S]
  have hU1 : 1 < U := (Real.one_lt_rpow hx hδ).trans_le hU
  have hV1 : 1 < Vr := (Real.one_lt_rpow hx hδ).trans_le hVr
  have huv : 0 < U*Vr := mul_pos (by linarith) (by linarith)
  have hV (j) : 0 < bandReciprocalMass (markedLogPowerBand (e j) x) :=
    (show 0 < Real.log 2/2 by positivity).trans (hb j).1
  have hid := markedPhysicalPositionMoment_eq_sourceDamping e x hx hdis hV ψ η d₀ Y
    ((Real.log x)^Qexp) q K U Vr hd₀ ((Real.exp_pos _).trans_le hY) hK hψsupport hU1 hV1 S hS w
  have hsource := hs d₀ Y hd₀.le hY hYhi hscale q U Vr hq0 hq1 hU hVr S hS w hw
  let R := markedPhysicalMomentTubeRadius (markedMemoryMomentLength x) K (d₀*Y)
  have hR : 1 ≤ R := markedPhysicalMomentTubeRadius_ge_one _ hK
    (mul_nonneg hd₀.le ((Real.exp_pos _).le.trans hY))
  let a := markedPhysicalSourceDampingGlobal e x ψ η d₀ Y ((Real.log x)^Qexp) q U Vr S hS (R := R) w
  let c := markedPhysicalCoordinateCappedGlobal e x ψ η d₀ Y ((Real.log x)^Qexp) q U Vr R hR
  let d := U*Vr/(riemannZeta 2).re
  have hreal : |a.re-d*c.re| ≤ ‖a-d • c‖ := by
    simpa only [Complex.sub_re,Complex.real_smul,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,sub_zero] using Complex.abs_re_le_norm (a-d • c)
  have hrealDiv := div_le_div_of_nonneg_right hreal huv.le
  have hresult : |a.re-d*c.re|/(U*Vr) ≤ (Real.log x)^(-G*(markedMemoryMomentLength x:ℝ)) :=
    hrealDiv.trans hsource
  exact (congrArg (fun t : ℝ => |t-d*c.re|/(U*Vr)) hid).le.trans hresult

end
end ArtinMatthews
