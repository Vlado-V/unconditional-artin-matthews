module

public import ArtinMatthews.MarkedPhysicalMomentCappedApproximation


set_option backward.privateInPublic true
@[expose] public section

/-! A name for the literal original full-box GSTSG matrix moment.
Its definition contains the original operator, endpoint projection,
constant physical mass and unnormalized position trace. -/
namespace ArtinMatthews
open scoped BigOperators Classical
noncomputable section
attribute [local instance] markedPhysicalMomentFintype markedPhysicalMomentDecidableEq

def markedPhysicalActualPositionMoment
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x : ℝ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q q U V : ℝ)
    (w : ↥(markedPhysicalPrimitiveBox U (16*U) V (2*V)) → ℤ × ℤ) : ℝ :=
  markedPhysicalPositionMoment (fun j => markedLogPowerBand (e j) x) (markedPadSlots x)
    (markedPhysicalPrimitiveBox U (16*U) V (2*V))
    (fun j => bandReciprocalMass (markedLogPowerBand (e j) x))
    (markedPhysicalRestrictedMatrix (fun j => markedLogPowerBand (e j) x)
      (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1)
      (fun j => bandReciprocalMass (markedLogPowerBand (e j) x))
      ⌊(Real.log x)^(1/100:ℝ)⌋₊ (markedPhysicalPrimitiveBox U (16*U) V (2*V))
      (fun _ hz => (Finset.mem_filter.mp hz).2) ψ η d₀ Y Q q
      (MarkedPhysicalActualGood e x d₀ Y w)) ⌈(Real.log x)^(1/2:ℝ)/2⌉₊

theorem markedPhysicalActualPositionMoment_nonneg
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x : ℝ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q q U V : ℝ)
    (w : ↥(markedPhysicalPrimitiveBox U (16*U) V (2*V)) → ℤ × ℤ) :
    0 ≤ markedPhysicalActualPositionMoment e x ψ η d₀ Y Q q U V w :=
  markedPhysicalPositionMoment_nonneg _ _ _ _ _ _

end
end ArtinMatthews
