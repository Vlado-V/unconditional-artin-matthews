module

public import ArtinMatthews.MarkedPhysicalSourceApproximation
public import ArtinMatthews.MarkedPhysicalRootDiscrepancyBudget
public import ArtinMatthews.MarkedPhysicalGlobalRootReplacement
public import ArtinMatthews.MarkedPhysicalSourceErrorScale


set_option backward.privateInPublic true
@[expose] public section

/-! The original full-box physical damping has a growing-moment
logarithmic approximation by the actual capped line main term. The
root density and original physical mass are retained. -/
namespace ArtinMatthews
open Filter
open scoped BigOperators Classical
noncomputable section

theorem markedPhysicalSourceDampingGlobal_capped_moment_log_saving
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j) (heUpper : ∀ j,e j ≤ (1/5:ℝ))
    (hinj : Function.Injective e) {δ : ℝ} (hδ : 0 < δ)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (K Hexp B etaBound psiBound Qexp G : ℝ)
    (hK : 0 ≤ K) (hHexp : 0 ≤ Hexp) (hB : 8 ≤ B)
    (heta : 0 ≤ etaBound) (hpsi : 0 ≤ psiBound) (hQexp : 0 ≤ Qexp) (hG : 0 ≤ G)
    (hη : ∀ t,‖η t‖ ≤ etaBound) (hψ : ∀ t,‖ψ t‖ ≤ psiBound) :
    ∀ᶠ x : ℝ in atTop,∀ (d₀ Y : ℝ) (hd₀ : 0 ≤ d₀)
      (hY : Real.exp ((Real.log x)^(1/10:ℝ)) ≤ Y), Y ≤ Real.exp (B*(Real.log x)^(1/5:ℝ)) →
      d₀*Y ≤ Real.exp (Hexp*(Real.log x)^(21/100:ℝ)) →
      ∀ (q U Vr : ℝ),0 ≤ q → q ≤ 1 → x^δ ≤ U → x^δ ≤ Vr →
      let R := markedPhysicalMomentTubeRadius (markedMemoryMomentLength x) K (d₀*Y)
      let hR := markedPhysicalMomentTubeRadius_ge_one (markedMemoryMomentLength x) hK
        (mul_nonneg hd₀ ((Real.exp_pos _).le.trans hY))
      ∀ (S : MarkedPhysicalLabelPath (fun j => markedLogPowerBand (e j) x)
        (markedPadSlots x) (markedMemoryMomentLength x) → ℕ) (hS : ∀ a,S a≠0)
        (w : ↥(markedPhysicalPrimitiveBox U (16*U) Vr (2*Vr)) → ℤ × ℤ),
        (∀ a,markedMinorIntegerDet a.1 (w a)=1) →
      ‖markedPhysicalSourceDampingGlobal e x ψ η d₀ Y ((Real.log x)^Qexp) q U Vr S hS (R := R) w-
        (U*Vr/(riemannZeta 2).re) •
          markedPhysicalCoordinateCappedGlobal e x ψ η d₀ Y ((Real.log x)^Qexp) q U Vr R hR‖ /
        (U*Vr) ≤ (Real.log x)^(-G*(markedMemoryMomentLength x:ℝ)) := by
  let F := 2+3/(riemannZeta 2).re
  let G₁ := G+1
  have hG₁ : 0 ≤ G₁ := by dsimp [G₁]; linarith
  have he0 : ∀ j,0 < e j := fun j => lt_of_lt_of_le (by norm_num) (he j)
  filter_upwards [markedPhysicalOddRootDiscrepancyMass_moment_log_saving e he heUpper hδ
      ψ η K Hexp B etaBound psiBound Qexp G₁ hK hHexp hB heta hpsi hQexp hG₁ hη hψ,
    markedPhysicalCoordinateBonferroniTailMass_moment_log_saving e he0 heUpper hinj ψ η
      K Hexp etaBound psiBound Qexp G₁ hK hHexp heta hpsi hQexp hG₁ hη hψ,
    markedPhysicalCoordinateRootGlobal_moment_log_saving e he heUpper hδ ψ η K Hexp B etaBound psiBound
      Qexp G₁ hK hHexp hB heta hpsi hQexp hG₁ hη hψ,
    markedPhysicalCoordinatePolynomialGlobal_moment_log_saving e he0 heUpper hinj ψ η
      K Hexp etaBound psiBound Qexp G₁ hK hHexp heta hpsi hQexp hG₁ hη hψ,
    markedPhysicalCoordinateGlobal_cap_difference_moment_log_saving e he heUpper hinj ψ η
      K Hexp etaBound psiBound Qexp G₁ hK hHexp heta hpsi hQexp hη hψ,
    marked_array_disjoint_eventually e hinj,eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (max 1 F))]
    with x hodd htail hroot hpoly hcap hdis hx hlog
  intro d₀ Y hd₀ hY hYhi hscale q U Vr hq0 hq1 hU hVr
  dsimp only
  intro S hS w hw
  let R := markedPhysicalMomentTubeRadius (markedMemoryMomentLength x) K (d₀*Y)
  have hlog1 : 1 ≤ Real.log x := (le_max_left _ _).trans hlog
  have hlogF : F ≤ Real.log x := (le_max_right _ _).trans hlog
  have hY1 : 1 ≤ Y := (Real.one_le_exp (Real.rpow_nonneg (zero_le_one.trans hlog1) _)).trans hY
  have hR : 1 ≤ R := markedPhysicalMomentTubeRadius_ge_one _ hK (mul_nonneg hd₀ (zero_le_one.trans hY1))
  have hU1 : 1 < U := (Real.one_lt_rpow hx hδ).trans_le hU
  have hV1 : 1 < Vr := (Real.one_lt_rpow hx hδ).trans_le hVr
  have huv : 0 < U*Vr := mul_pos (by linarith) (by linarith)
  have hn : 0 < markedMemoryMomentLength x := markedPhysicalMomentLength_pos hx
  let d := U*Vr/(riemannZeta 2).re
  have hd : 0 ≤ d := div_nonneg huv.le markedRoot_zeta_two_pos.le
  let p := (Real.log x)^(-G₁*(markedMemoryMomentLength x:ℝ))
  let a := markedPhysicalSourceDampingGlobal e x ψ η d₀ Y ((Real.log x)^Qexp) q U Vr S hS (R := R) w
  let b := markedPhysicalCoordinateRootGlobal e x ψ η d₀ Y ((Real.log x)^Qexp) hR q U Vr
    (2*markedPhysicalBonferroniDepth x)
  let c := markedPhysicalCoordinatePolynomialGlobal e x ψ η d₀ Y ((Real.log x)^Qexp) q U Vr R hR
  let i := markedPhysicalCoordinateIndependentGlobal e x ψ η d₀ Y ((Real.log x)^Qexp) q U Vr R hR
  let z := markedPhysicalCoordinateCappedGlobal e x ψ η d₀ Y ((Real.log x)^Qexp) q U Vr R hR
  let m := markedPhysicalOddRootDiscrepancyMass e x ψ η d₀ Y ((Real.log x)^Qexp) hR q U Vr
  let t := markedPhysicalCoordinateBonferroniTailMass e x ψ η d₀ Y ((Real.log x)^Qexp) q U Vr R hR
  have hm : m ≤ p*(U*Vr) := (div_le_iff₀ huv).mp
    (hodd d₀ Y hd₀ hY hYhi hscale q U Vr hq0 hq1 hU hVr)
  have ht : t ≤ p := htail d₀ Y hd₀ hY1 hscale q U Vr hq0 hq1
  have hr : ‖b-d • c‖ ≤ p*(U*Vr) := (div_le_iff₀ huv).mp
    (hroot d₀ Y hd₀ hY hYhi hscale q U Vr hq0 hq1 hU hVr)
  have hp : ‖c-i‖ ≤ p := by
    simpa only [norm_sub_rev] using hpoly d₀ Y hd₀ hY1 hscale q U Vr hq0 hq1
  have hc : ‖i-z‖ ≤ p := hcap d₀ Y hd₀ hY1 hscale q U Vr hq0 hq1
  have hab : ‖a-b‖ ≤ m+d*t := markedPhysicalSourceDampingGlobal_root_error e x ψ η
    d₀ Y ((Real.log x)^Qexp) q U Vr S hS hR hdis hn hU1 hV1 w hw hq0 hq1
  have hci : ‖d • c-d • i‖ ≤ d*p := by
    rw [← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_nonneg hd]
    exact mul_le_mul_of_nonneg_left hp hd
  have hiz : ‖d • i-d • z‖ ≤ d*p := by
    rw [← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_nonneg hd]
    exact mul_le_mul_of_nonneg_left hc hd
  have hdt : d*t ≤ d*p := mul_le_mul_of_nonneg_left ht hd
  have hsum := markedPhysical_norm_four_differences a b (d • c) (d • i) (d • z)
  have hb : ‖a-d • z‖ ≤ 2*(p*(U*Vr))+3*(d*p) := by linarith
  have heq : 2*(p*(U*Vr))+3*(d*p)=(F*p)*(U*Vr) := by dsimp [F,d]; ring
  change ‖a-d • z‖/(U*Vr) ≤ _
  apply ((div_le_iff₀ huv).mpr (hb.trans_eq heq)).trans
  exact markedPhysicalSourceErrorScale hlog1 hlogF hn

end
end ArtinMatthews
