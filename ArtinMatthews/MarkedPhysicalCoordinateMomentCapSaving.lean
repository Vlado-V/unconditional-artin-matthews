module

public import ArtinMatthews.MarkedPhysicalCoordinateGlobalEnvelope
public import ArtinMatthews.MarkedPhysicalCoordinateLineGlobal
public import ArtinMatthews.MarkedPhysicalMomentCapacitySaving


set_option backward.privateInPublic true
@[expose] public section

/-! The globally summed actual small-B correction has the strength
needed before taking the growing moment root. The actual factor 15,
physical mass and full coefficient sum are discharged by source bounds. -/
namespace ArtinMatthews
open Filter
open scoped BigOperators Classical
noncomputable section

theorem markedPhysicalCoordinateCapacityGlobal_moment_log_saving
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he0 : ∀ j,(1/10:ℝ)≤e j) (he1 : ∀ j,e j≤(1/5:ℝ))
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (K Hexp etaBound psiBound Qexp G : ℝ)
    (hK : 0≤K) (hHexp : 0≤Hexp) (heta : 0≤etaBound) (hpsi : 0≤psiBound)
    (hQexp : 0≤Qexp) (hη : ∀ t,‖η t‖≤etaBound) (hψ : ∀ t,‖ψ t‖≤psiBound) :
    ∀ᶠ x : ℝ in atTop,∀ (d₀ Y : ℝ) (hd₀ : 0≤d₀) (hY : 1≤Y),
      d₀*Y≤Real.exp (Hexp*(Real.log x)^(21/100:ℝ)) → ∀ (q U W : ℝ),0≤q → q≤1 →
      ‖markedPhysicalCoordinateCapacityGlobal e x ψ η d₀ Y ((Real.log x)^Qexp) q U W
        (markedPhysicalMomentTubeRadius (markedMemoryMomentLength x) K (d₀*Y))
        (markedPhysicalMomentTubeRadius_ge_one _ hK (mul_nonneg hd₀ (zero_le_one.trans hY)))‖≤
          (Real.log x)^(-G*(markedMemoryMomentLength x:ℝ)) := by
  filter_upwards [markedPhysicalCoordinateCapacityGlobal_envelope e he0,
    markedPhysicalCoordinateCapacity_actual_moment_log_saving e he0 he1 ψ η K Hexp etaBound psiBound Qexp 15 G
      (by norm_num) hK hHexp heta hpsi hQexp hη hψ] with x he ht
  intro d₀ Y hd₀ hY hscale q U W hq0 hq1
  apply (he ψ η d₀ Y ((Real.log x)^Qexp) q U W hq0 hq1
    (markedPhysicalMomentTubeRadius (markedMemoryMomentLength x) K (d₀*Y))
    (markedPhysicalMomentTubeRadius_ge_one _ hK (mul_nonneg hd₀ (zero_le_one.trans hY)))).trans
  simpa only [mul_assoc] using ht d₀ Y hd₀ hY hscale

theorem markedPhysicalCoordinateGlobal_cap_difference_moment_log_saving
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
        markedPhysicalCoordinateCappedGlobal e x ψ η d₀ Y ((Real.log x)^Qexp) q U W B hB‖≤
          (Real.log x)^(-G*(markedMemoryMomentLength x:ℝ)) := by
  filter_upwards [markedPhysicalCoordinateGlobal_actual_cap_split e he0 hinj,
    markedPhysicalCoordinateCapacityGlobal_moment_log_saving e he0 he1 ψ η K Hexp etaBound psiBound Qexp G
      hK hHexp heta hpsi hQexp hη hψ] with x hs he
  intro d₀ Y hd₀ hY hscale q U W hq0 hq1
  dsimp only
  rw [hs ψ η d₀ Y ((Real.log x)^Qexp) q U W hq0 hq1,add_sub_cancel_left]
  exact he d₀ Y hd₀ hY hscale q U W hq0 hq1

end
end ArtinMatthews
