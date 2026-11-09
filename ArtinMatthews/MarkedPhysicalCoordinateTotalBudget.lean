module

public import ArtinMatthews.MarkedPhysicalCoordinateIndexBudget
public import ArtinMatthews.MarkedPhysicalCoordinateWeightBudget
public import ArtinMatthews.MarkedPhysicalCoordinateIndexCoefficient


set_option backward.privateInPublic true
@[expose] public section

/-! The complete finite relative-coordinate, ordered-label and copied-
slot coefficient norm sum, multiplied by the original physical mass,
has an explicit sub-log-squared cost. Every cardinal and kernel factor
is the literal one on the actual carrier. -/
namespace ArtinMatthews
noncomputable section
open Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

def markedPhysicalCoordinateTotalCost (groups : ℕ) (K Hexp etaBound psiBound Qexp : ℝ) : ℝ :=
  markedPhysicalCoordinateIndexCost groups K Hexp+
    markedPhysicalCoordinateWeightCost groups etaBound psiBound Qexp

theorem markedPhysicalCoordinateTotalCost_nonneg (groups : ℕ) (etaBound : ℝ)
    {K Hexp psiBound Qexp : ℝ} (hK : 0 ≤ K) (hHexp : 0 ≤ Hexp)
    (hpsi : 0 ≤ psiBound) (hQexp : 0 ≤ Qexp) :
    0 ≤ markedPhysicalCoordinateTotalCost groups K Hexp etaBound psiBound Qexp :=
  add_nonneg (markedPhysicalCoordinateIndexCost_nonneg groups hK hHexp)
    (markedPhysicalCoordinateWeightCost_nonneg groups etaBound hpsi hQexp)

theorem markedPhysicalCoordinateCoefficient_actual_total_budget
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he0 : ∀ j,0 < e j) (he1 : ∀ j,e j ≤ (1/5:ℝ))
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (K Hexp etaBound psiBound Qexp : ℝ)
    (hK : 0 ≤ K) (hHexp : 0 ≤ Hexp) (heta : 0 ≤ etaBound) (hpsi : 0 ≤ psiBound)
    (hQexp : 0 ≤ Qexp) (hη : ∀ t,‖η t‖ ≤ etaBound) (hψ : ∀ t,‖ψ t‖ ≤ psiBound) :
    ∀ᶠ x : ℝ in atTop, ∀ (d₀ Y : ℝ),0 ≤ d₀ → 1 ≤ Y →
      d₀*Y ≤ Real.exp (Hexp*(Real.log x)^(21/100:ℝ)) →
      markedPhysicalMass (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) (markedPadSlots x) *
        (∑ i : MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x)
            (markedPadSlots x) (markedMemoryMomentLength x)
            (markedPhysicalMomentTubeRadius (markedMemoryMomentLength x) K (d₀*Y)),
          ‖markedPhysicalCoordinateIndexCoefficient (fun j => markedLogPowerBand (e j) x)
            (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1)
            (fun j => bandReciprocalMass (markedLogPowerBand (e j) x))
            ⌊(Real.log x)^(1/100:ℝ)⌋₊ ψ η d₀ Y ((Real.log x)^Qexp) i‖) ≤
      Real.exp (markedPhysicalCoordinateTotalCost (Fintype.card J) K Hexp etaBound psiBound Qexp *
        (Real.log x)^(3/2:ℝ)) := by
  filter_upwards [markedPhysicalCoordinateWeight_actual_budget e he0 etaBound psiBound Qexp hpsi hQexp,
    markedPhysicalActualNormalizer_bounds e he0 etaBound psiBound hpsi,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with x hw hn hlog
  intro d₀ Y hd₀ hY hscale
  have hL : 0 < Real.log x := by linarith
  have hQ : 1 ≤ (Real.log x)^Qexp := Real.one_le_rpow hlog hQexp
  have hσ := (hn.1 (markedPadSlots x)).1
  have hcoeff := markedPhysicalCoordinateIndexCoefficient_absolute_sum
    (fun j => markedLogPowerBand (e j) x) (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1)
    (fun j => bandReciprocalMass (markedLogPowerBand (e j) x))
    ⌊(Real.log x)^(1/100:ℝ)⌋₊ ψ η d₀ Y ((Real.log x)^Qexp) etaBound psiBound
    hY hQ heta hpsi hη hψ (markedMemoryMomentLength x)
    (markedPhysicalMomentTubeRadius (markedMemoryMomentLength x) K (d₀*Y))
  have hcard := markedPhysicalCoordinateIndex_actual_card_bound e hlog he1 hK
    (mul_nonneg hd₀ (zero_le_one.trans hY)) hHexp hscale
  have hIcost := markedPhysicalCoordinateIndexCost_nonneg (Fintype.card J) hK hHexp
  have hLpow : Real.log x ≤ (Real.log x)^(3/2:ℝ) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hlog (by norm_num : (1:ℝ) ≤ 3/2)
  calc
    _ ≤ markedPhysicalMass (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) (markedPadSlots x) *
        ((Fintype.card (MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x)
          (markedPadSlots x) (markedMemoryMomentLength x)
          (markedPhysicalMomentTubeRadius (markedMemoryMomentLength x) K (d₀*Y))):ℝ) *
          (markedPhysicalCoordinateEdgeBound (fun j => bandReciprocalMass (markedLogPowerBand (e j) x))
            etaBound psiBound*((Real.log x)^Qexp)^3)^(markedMemoryMomentLength x)) :=
      mul_le_mul_of_nonneg_left hcoeff hσ
    _ = (Fintype.card (MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x)
          (markedPadSlots x) (markedMemoryMomentLength x)
          (markedPhysicalMomentTubeRadius (markedMemoryMomentLength x) K (d₀*Y))):ℝ) *
        (markedPhysicalMass (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) (markedPadSlots x) *
          (markedPhysicalCoordinateEdgeBound (fun j => bandReciprocalMass (markedLogPowerBand (e j) x))
            etaBound psiBound*((Real.log x)^Qexp)^3)^(markedMemoryMomentLength x)) := by ring
    _ ≤ Real.exp (markedPhysicalCoordinateIndexCost (Fintype.card J) K Hexp*Real.log x) *
        Real.exp (markedPhysicalCoordinateWeightCost (Fintype.card J) etaBound psiBound Qexp*(Real.log x)^(3/2:ℝ)) :=
      mul_le_mul hcard hw (by unfold markedPhysicalCoordinateEdgeBound; positivity) (Real.exp_nonneg _)
    _ ≤ Real.exp (markedPhysicalCoordinateIndexCost (Fintype.card J) K Hexp*(Real.log x)^(3/2:ℝ)) *
        Real.exp (markedPhysicalCoordinateWeightCost (Fintype.card J) etaBound psiBound Qexp*(Real.log x)^(3/2:ℝ)) :=
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hLpow hIcost)) (Real.exp_nonneg _)
    _ = _ := by
      rw [← Real.exp_add]
      congr 1
      unfold markedPhysicalCoordinateTotalCost
      ring

end
end ArtinMatthews
