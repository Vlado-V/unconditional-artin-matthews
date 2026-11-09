module

public import ArtinMatthews.MarkedPhysicalCoordinateCapacityGlobal


set_option backward.privateInPublic true
@[expose] public section

/-! The globally summed actual correction has its literal scalar
majorant exposed, so stronger source asymptotics can be applied without
replacing the physical mass, carrier or coefficient norm sum. -/
namespace ArtinMatthews
open Filter
open scoped BigOperators Classical
noncomputable section

theorem markedPhysicalCoordinateCapacityGlobal_envelope
    {J : Type*} [Fintype J] [DecidableEq J] (e : J → ℝ) (he : ∀ j,(1/10:ℝ)≤e j) :
    ∀ᶠ x : ℝ in atTop,∀ (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q U W : ℝ),
      0≤q → q≤1 → ∀ (B : ℕ) (hB : 1≤B),
      ‖markedPhysicalCoordinateCapacityGlobal e x ψ η d₀ Y Q q U W B hB‖≤
        15*(markedPhysicalMass (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) (markedPadSlots x)*
          (∑ i : MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x)
            (markedPadSlots x) (markedMemoryMomentLength x) B,
            ‖markedPhysicalCoordinateIndexCoefficient (fun j => markedLogPowerBand (e j) x)
              (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1)
              (fun j => bandReciprocalMass (markedLogPowerBand (e j) x))
              ⌊(Real.log x)^(1/100:ℝ)⌋₊ ψ η d₀ Y Q i‖))*
          markedMemoryOrphanTailEnvelope (80*(Fintype.card J:ℝ)) 1 x := by
  filter_upwards [markedPhysicalCoordinateCapacityTerm_envelope e he] with x ht
  intro ψ η d₀ Y Q q U W hq0 hq1 B hB
  let V := fun j => bandReciprocalMass (markedLogPowerBand (e j) x)
  have hv : ∀ j,0≤V j := by intro j; unfold V bandReciprocalMass; positivity
  have hm : 0 ≤ markedPhysicalMass V (markedPadSlots x) := markedPhysicalMass_nonneg V _ hv
  have hs := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => ht V ψ η d₀ Y Q q U W hq0 hq1 B hB i)
  rw [← Finset.mul_sum] at hs
  unfold markedPhysicalCoordinateCapacityGlobal
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hm]
  apply ((mul_le_mul_of_nonneg_left (norm_sum_le _ _) hm).trans
    (mul_le_mul_of_nonneg_left hs hm)).trans_eq
  ring

end
end ArtinMatthews
