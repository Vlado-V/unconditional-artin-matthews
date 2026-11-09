module

public import ArtinMatthews.MarkedPhysicalCoordinateCapacityGlobal
public import ArtinMatthews.MarkedPhysicalCoordinateActualCapSplit


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine finite independent-line main term differs from its
literal small-B capped version by the actual globally summed correction.
No identity with the physical root sum or tilted memory word is assumed. -/
namespace ArtinMatthews
open Filter
open scoped BigOperators Classical
noncomputable section

def markedPhysicalCoordinateIndependentGlobal {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x : ℝ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q q U W : ℝ) (B : ℕ) (hB : 1≤B) : ℂ :=
  (markedPhysicalMass (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) (markedPadSlots x):ℂ)*
    ∑ i : MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x)
      (markedPadSlots x) (markedMemoryMomentLength x) B,
      markedPhysicalCoordinateIndependentTerm e x
        (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) ψ η d₀ Y Q i hB q U W

def markedPhysicalCoordinateCappedGlobal {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x : ℝ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q q U W : ℝ) (B : ℕ) (hB : 1≤B) : ℂ :=
  (markedPhysicalMass (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) (markedPadSlots x):ℂ)*
    ∑ i : MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x)
      (markedPadSlots x) (markedMemoryMomentLength x) B,
      markedPhysicalCoordinateCappedTerm e x
        (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) ψ η d₀ Y Q i hB q U W
        (markedDirtyMemoryCutoff x)

theorem markedPhysicalCoordinateGlobal_actual_cap_split
    {J : Type*} [Fintype J] [DecidableEq J] (e : J → ℝ)
    (he : ∀ j,(1/10:ℝ)≤e j) (hinj : Function.Injective e) :
    ∀ᶠ x : ℝ in atTop,∀ (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q U W : ℝ),
      0≤q → q≤1 → ∀ (B : ℕ) (hB : 1≤B),
      markedPhysicalCoordinateIndependentGlobal e x ψ η d₀ Y Q q U W B hB=
        markedPhysicalCoordinateCappedGlobal e x ψ η d₀ Y Q q U W B hB+
        markedPhysicalCoordinateCapacityGlobal e x ψ η d₀ Y Q q U W B hB := by
  filter_upwards [markedPhysicalCoordinateLineTerm_actual_cap_split e he hinj] with x hx
  intro ψ η d₀ Y Q q U W hq0 hq1 B hB
  unfold markedPhysicalCoordinateIndependentGlobal markedPhysicalCoordinateCappedGlobal
    markedPhysicalCoordinateCapacityGlobal
  rw [← mul_add,← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact hx _ ψ η d₀ Y Q q U W hq0 hq1 B hB i (markedDirtyMemoryCutoff x)

theorem markedPhysicalCoordinateGlobal_cap_difference_log_saving
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he0 : ∀ j,(1/10:ℝ)≤e j) (he1 : ∀ j,e j≤(1/5:ℝ)) (hinj : Function.Injective e)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (K Hexp etaBound psiBound Qexp G : ℝ)
    (hK : 0≤K) (hHexp : 0≤Hexp) (heta : 0≤etaBound) (hpsi : 0≤psiBound)
    (hQexp : 0≤Qexp) (hη : ∀ t,‖η t‖≤etaBound) (hψ : ∀ t,‖ψ t‖≤psiBound) :
    ∀ᶠ x : ℝ in atTop,∀ (d₀ Y : ℝ) (hd₀ : 0≤d₀) (hY : 1≤Y),
      d₀*Y≤Real.exp (Hexp*(Real.log x)^(21/100:ℝ)) → ∀ (q U W : ℝ),0≤q → q≤1 →
      let B := markedPhysicalMomentTubeRadius (markedMemoryMomentLength x) K (d₀*Y)
      let hB := markedPhysicalMomentTubeRadius_ge_one (markedMemoryMomentLength x) hK
        (mul_nonneg hd₀ (zero_le_one.trans hY))
      ‖markedPhysicalCoordinateIndependentGlobal e x ψ η d₀ Y ((Real.log x)^Qexp) q U W B hB-
        markedPhysicalCoordinateCappedGlobal e x ψ η d₀ Y ((Real.log x)^Qexp) q U W B hB‖≤(Real.log x)^(-G) := by
  filter_upwards [markedPhysicalCoordinateGlobal_actual_cap_split e he0 hinj,
    markedPhysicalCoordinateCapacityGlobal_log_saving e he0 he1 ψ η K Hexp etaBound psiBound Qexp G
      hK hHexp heta hpsi hQexp hη hψ] with x hsplit herr
  intro d₀ Y hd₀ hY hscale q U W hq0 hq1
  dsimp only
  rw [hsplit ψ η d₀ Y ((Real.log x)^Qexp) q U W hq0 hq1]
  rw [add_sub_cancel_left]
  exact herr d₀ Y hd₀ hY hscale q U W hq0 hq1

end
end ArtinMatthews
