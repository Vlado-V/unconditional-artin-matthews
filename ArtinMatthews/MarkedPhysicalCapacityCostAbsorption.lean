module

public import ArtinMatthews.MarkedPhysicalCoordinateTotalBudget
public import ArtinMatthews.MarkedMemoryOrphanTailDecay


set_option backward.privateInPublic true
@[expose] public section

/-! The actual finite coefficient norm sum and original physical mass
are absorbed by the actual small-B orphan envelope. All carrier, band,
kernel and source-hierarchy estimates are derived in the imported
concrete budgets; there is no abstract cardinal or weight premise. -/
namespace ArtinMatthews
noncomputable section
open Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

def markedPhysicalCoordinateCapacityCost (groups : ℕ) (K Hexp etaBound psiBound Qexp : ℝ) : ℝ :=
  markedPhysicalCoordinateTotalCost groups K Hexp etaBound psiBound Qexp+80*(groups:ℝ)

theorem markedPhysicalCoordinateCapacityCost_absorb
    (groups : ℕ) (K Hexp etaBound psiBound Qexp : ℝ) {x : ℝ} (hlog : 1 ≤ Real.log x) :
    Real.exp (markedPhysicalCoordinateTotalCost groups K Hexp etaBound psiBound Qexp*(Real.log x)^(3/2:ℝ)) *
      markedMemoryOrphanTailEnvelope (80*(groups:ℝ)) 1 x ≤
    markedMemoryOrphanTailEnvelope (markedPhysicalCoordinateCapacityCost groups K Hexp etaBound psiBound Qexp)
      (3/2:ℝ) x := by
  have hp : Real.log x ≤ (Real.log x)^(3/2:ℝ) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hlog (by norm_num : (1:ℝ) ≤ 3/2)
  have hh := mul_le_mul_of_nonneg_left hp (show 0 ≤ 80*(groups:ℝ) by positivity)
  unfold markedMemoryOrphanTailEnvelope
  rw [Real.rpow_one,← mul_div_assoc,← Real.exp_add]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Real.exp_le_exp.mpr
  unfold markedPhysicalCoordinateCapacityCost
  nlinarith

theorem markedPhysicalCoordinateCapacity_actual_log_saving
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he0 : ∀ j,(1/10:ℝ) ≤ e j) (he1 : ∀ j,e j ≤ (1/5:ℝ))
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (K Hexp etaBound psiBound Qexp G : ℝ)
    (hK : 0 ≤ K) (hHexp : 0 ≤ Hexp) (heta : 0 ≤ etaBound) (hpsi : 0 ≤ psiBound)
    (hQexp : 0 ≤ Qexp) (hη : ∀ t,‖η t‖ ≤ etaBound) (hψ : ∀ t,‖ψ t‖ ≤ psiBound) :
    ∀ᶠ x : ℝ in atTop, ∀ (d₀ Y : ℝ),0 ≤ d₀ → 1 ≤ Y →
      d₀*Y ≤ Real.exp (Hexp*(Real.log x)^(21/100:ℝ)) →
      (markedPhysicalMass (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) (markedPadSlots x) *
        (∑ i : MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x)
            (markedPadSlots x) (markedMemoryMomentLength x)
            (markedPhysicalMomentTubeRadius (markedMemoryMomentLength x) K (d₀*Y)),
          ‖markedPhysicalCoordinateIndexCoefficient (fun j => markedLogPowerBand (e j) x)
            (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1)
            (fun j => bandReciprocalMass (markedLogPowerBand (e j) x))
            ⌊(Real.log x)^(1/100:ℝ)⌋₊ ψ η d₀ Y ((Real.log x)^Qexp) i‖)) *
        markedMemoryOrphanTailEnvelope (80*(Fintype.card J:ℝ)) 1 x ≤ (Real.log x)^(-G) := by
  have hepos : ∀ j,0 < e j := fun j => by linarith [he0 j]
  filter_upwards [markedPhysicalCoordinateCoefficient_actual_total_budget e hepos he1 ψ η K Hexp
      etaBound psiBound Qexp hK hHexp heta hpsi hQexp hη hψ,
    markedMemoryOrphanTailEnvelope_log_saving
      (markedPhysicalCoordinateCapacityCost (Fintype.card J) K Hexp etaBound psiBound Qexp)
      (3/2:ℝ) G (by norm_num),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with x ht he hlog
  intro d₀ Y hd₀ hY hscale
  have henv : 0 ≤ markedMemoryOrphanTailEnvelope (80*(Fintype.card J:ℝ)) 1 x := by
    unfold markedMemoryOrphanTailEnvelope
    positivity
  exact ((mul_le_mul_of_nonneg_right (ht d₀ Y hd₀ hY hscale) henv).trans
    (markedPhysicalCoordinateCapacityCost_absorb (Fintype.card J) K Hexp etaBound psiBound Qexp hlog)).trans he

end
end ArtinMatthews
