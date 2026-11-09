module

public import ArtinMatthews.MarkedPhysicalSelectedMeanBounds
public import ArtinMatthews.MarkedPhysicalCoordinateBonferroniTail


set_option backward.privateInPublic true
@[expose] public section

/-! The norm mass of the averaged odd tail is bounded by the genuine
selected-modulus tail mean with the original physical coefficient mass. -/
namespace ArtinMatthews
open scoped BigOperators Classical
noncomputable section

def markedPhysicalSelectedAverageTailMass
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x : ℝ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q q U Vr : ℝ) {R : ℕ} (hR : 1 ≤ R) (k : ℕ) : ℝ :=
  markedPhysicalMass (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) (markedPadSlots x)*
    ∑ i : MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x)
        (markedPadSlots x) (markedMemoryMomentLength x) R,
      ∑ T ∈ (markedPhysicalBandPrimes (fun j => markedLogPowerBand (e j) x) \
          markedPhysicalPathUsedPrimes Finset.univ i.1).powersetCard k,
        ‖markedPhysicalCoordinateSelectedAverage e x
          (fun j => bandReciprocalMass (markedLogPowerBand (e j) x))
          ψ η d₀ Y Q i hR q U Vr T‖

theorem markedPhysicalSelectedAverageTailMass_le
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x : ℝ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q q U Vr : ℝ) {R : ℕ} (hR : 1 ≤ R)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hUV : 0 ≤ U*Vr) :
    markedPhysicalSelectedAverageTailMass e x ψ η d₀ Y Q q U Vr hR
        (2*markedPhysicalBonferroniDepth x+1) ≤
      (U*Vr/(riemannZeta 2).re)*
        markedPhysicalCoordinateBonferroniTailMass e x ψ η d₀ Y Q q U Vr R hR := by
  have hm : 0 ≤ markedPhysicalMass
      (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) (markedPadSlots x) :=
    markedPhysicalMass_nonneg _ _ (fun _ => by unfold bandReciprocalMass; positivity)
  unfold markedPhysicalSelectedAverageTailMass markedPhysicalCoordinateBonferroniTailMass
    markedPhysicalCoordinateIndexTailMean markedPhysicalBonferroniTailMean
  rw [mul_left_comm (U*Vr/(riemannZeta 2).re)]
  apply mul_le_mul_of_nonneg_left _ hm
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro T hT
  exact (markedPhysicalCoordinateSelectedAverage_norm_le e x _ ψ η d₀ Y Q i hR q U Vr hq0 hq1 hUV T
    (fun p hp => (Finset.mem_sdiff.mp ((Finset.mem_powersetCard.mp hT).1 hp)).1)).trans_eq (by ring)

end
end ArtinMatthews
