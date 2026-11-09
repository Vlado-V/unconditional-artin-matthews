module

public import ArtinMatthews.MarkedPhysicalCoordinateLineTerms
public import ArtinMatthews.MarkedMemoryActualCapacityCorrection


set_option backward.privateInPublic true
@[expose] public section

/-! The actual omitted-cap correction on each fixed-coordinate row
inherits the proved original small-B envelope, including the true good
volume. The normalized box has mass 15, retained explicitly. -/
namespace ArtinMatthews
open Filter
open scoped BigOperators Classical
noncomputable section

theorem markedPhysicalCoordinateCapacityTerm_envelope
    {J : Type*} [Fintype J] [DecidableEq J] (e : J → ℝ) (he : ∀ j,(1/10:ℝ)≤e j) :
    ∀ᶠ x : ℝ in atTop,∀ (V : J → ℝ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
      (d₀ Y Q q U W : ℝ),0≤q → q≤1 → ∀ (B : ℕ) (hB : 1≤B)
      (i : MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x)
        (markedPadSlots x) (markedMemoryMomentLength x) B),
      ‖markedPhysicalCoordinateCapacityTerm e x V ψ η d₀ Y Q i hB q U W (markedDirtyMemoryCutoff x)‖≤
        15*markedMemoryOrphanTailEnvelope (80*(Fintype.card J:ℝ)) 1 x*
          ‖markedPhysicalCoordinateIndexCoefficient (fun j => markedLogPowerBand (e j) x)
            (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) V ⌊(Real.log x)^(1/100:ℝ)⌋₊ ψ η d₀ Y Q i‖ := by
  filter_upwards [markedMemoryActualCapacityCorrection_envelope e he] with x hx
  intro V ψ η d₀ Y Q q U W hq0 hq1 B hB i
  have hv := markedPhysicalCoordinateIndexGoodVolume_bounds e x d₀ Y U W i hB
  have he0 : 0 ≤ markedMemoryOrphanTailEnvelope (80*(Fintype.card J:ℝ)) 1 x := by
    unfold markedMemoryOrphanTailEnvelope
    positivity
  unfold markedPhysicalCoordinateCapacityTerm markedPhysicalCoordinatePathApply
  split_ifs with ha hc hloop
  · dsimp only
    let d := markedPhysicalCoordinateIndexActivePath (fun j => markedLogPowerBand (e j) x)
      (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) V ⌊(Real.log x)^(1/100:ℝ)⌋₊ ψ η d₀ Y Q i hB ha hc
    let c := markedPhysicalCoordinateIndexCoefficient (fun j => markedLogPowerBand (e j) x)
      (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) V ⌊(Real.log x)^(1/100:ℝ)⌋₊ ψ η d₀ Y Q i
    let v := markedPhysicalCoordinateIndexGoodVolume e x d₀ Y U W i hB
    have hvn : ‖(v:ℂ)‖≤15 := by
      simpa only [v,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hv.1] using hv.2
    have hh := hx q hq0 hq1 (markedPrimitiveCoordinateTube B)
      (fun z hz => ((markedPrimitiveCoordinateTube_mem B z).mp hz).2.2)
      d c
    calc
      _ = ‖(v:ℂ)‖*‖markedMemoryPathCapacityCorrection
        (fun z hz => ((markedPrimitiveCoordinateTube_mem B z).mp hz).2.2) d q (markedDirtyMemoryCutoff x) c‖ :=
        norm_mul _ _
      _ ≤ 15*(markedMemoryOrphanTailEnvelope (80*(Fintype.card J:ℝ)) 1 x*
          ‖markedPhysicalCoordinateIndexCoefficient (fun j => markedLogPowerBand (e j) x)
            (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) V ⌊(Real.log x)^(1/100:ℝ)⌋₊ ψ η d₀ Y Q i‖) :=
        mul_le_mul hvn hh (norm_nonneg _) (by norm_num : (0:ℝ)≤15)
      _ = _ := by ring
  all_goals rw [norm_zero]; positivity

end
end ArtinMatthews
