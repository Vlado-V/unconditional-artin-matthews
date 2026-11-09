module

public import ArtinMatthews.MarkedPhysicalRootDiscrepancyMass
public import ArtinMatthews.MarkedPhysicalSelectedAverageTail


set_option backward.privateInPublic true
@[expose] public section

/-! Absolute root-tail mass is controlled by its actual discrepancy
and the nonnegative averaged tail. No signed cancellation is used. -/
namespace ArtinMatthews
open scoped BigOperators Classical
noncomputable section

def markedPhysicalSelectedRootTailNormMass
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x : ℝ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q q U Vr : ℝ) {R : ℕ} (hR : 1 ≤ R) (k : ℕ) : ℝ :=
  markedPhysicalMass (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) (markedPadSlots x)*
    ∑ i : MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x)
        (markedPadSlots x) (markedMemoryMomentLength x) R,
      ∑ T ∈ (markedPhysicalBandPrimes (fun j => markedLogPowerBand (e j) x) \
          markedPhysicalPathUsedPrimes Finset.univ i.1).powersetCard k,
        ‖markedPhysicalCoordinateSelectedRoot e x
          (fun j => bandReciprocalMass (markedLogPowerBand (e j) x))
          ψ η d₀ Y Q i hR q U Vr T‖

theorem markedPhysicalSelectedRootTailNormMass_le
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x : ℝ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q q U Vr : ℝ) {R : ℕ} (hR : 1 ≤ R) (k : ℕ) :
    markedPhysicalSelectedRootTailNormMass e x ψ η d₀ Y Q q U Vr hR k ≤
      markedPhysicalCoordinateDiscrepancyMass e x ψ η d₀ Y Q hR q U Vr k+
      markedPhysicalSelectedAverageTailMass e x ψ η d₀ Y Q q U Vr hR k := by
  have hm : 0 ≤ markedPhysicalMass
      (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) (markedPadSlots x) :=
    markedPhysicalMass_nonneg _ _ (fun _ => by unfold bandReciprocalMass; positivity)
  unfold markedPhysicalSelectedRootTailNormMass markedPhysicalCoordinateDiscrepancyMass
    markedPhysicalSelectedAverageTailMass
  rw [← mul_add,← Finset.sum_add_distrib]
  apply mul_le_mul_of_nonneg_left _ hm
  apply Finset.sum_le_sum
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro T _
  exact norm_le_norm_sub_add _ _

theorem markedPhysicalSelectedRootOddTailNormMass_le
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x : ℝ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q q U Vr : ℝ) {R : ℕ} (hR : 1 ≤ R)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hUV : 0 ≤ U*Vr) :
    markedPhysicalSelectedRootTailNormMass e x ψ η d₀ Y Q q U Vr hR
        (2*markedPhysicalBonferroniDepth x+1) ≤
      markedPhysicalOddRootDiscrepancyMass e x ψ η d₀ Y Q hR q U Vr+
      (U*Vr/(riemannZeta 2).re)*
        markedPhysicalCoordinateBonferroniTailMass e x ψ η d₀ Y Q q U Vr R hR :=
by
  let k := 2*markedPhysicalBonferroniDepth x+1
  let a := markedPhysicalSelectedRootTailNormMass e x ψ η d₀ Y Q q U Vr hR k
  let b := markedPhysicalCoordinateDiscrepancyMass e x ψ η d₀ Y Q hR q U Vr k
  let c := markedPhysicalSelectedAverageTailMass e x ψ η d₀ Y Q q U Vr hR k
  let d := (U*Vr/(riemannZeta 2).re)*
    markedPhysicalCoordinateBonferroniTailMass e x ψ η d₀ Y Q q U Vr R hR
  have ha : a ≤ b+c := markedPhysicalSelectedRootTailNormMass_le e x ψ η d₀ Y Q q U Vr hR k
  have hc : c ≤ d := markedPhysicalSelectedAverageTailMass_le e x ψ η d₀ Y Q q U Vr hR hq0 hq1 hUV
  change a ≤ b+d
  linarith


end
end ArtinMatthews
