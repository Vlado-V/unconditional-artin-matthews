module

public import ArtinMatthews.MarkedPhysicalDetectorKernel
public import ArtinMatthews.MarkedPhysicalTypeIIGoodRemoval
public import ArtinMatthews.MarkedPhysicalCharacterGoodRemoval


set_option backward.privateInPublic true
@[expose] public section

/-! The literal unprojected physical endpoint pairing is independent of
its damping parameter. This allows a strict Schur-gap damping in the
moment proof and returns to the original detector pairing at one. -/
namespace ArtinMatthews
open scoped BigOperators Classical
noncomputable section
attribute [local instance] markedPhysicalMomentFintype markedPhysicalMomentDecidableEq

theorem markedPhysicalEdgePairing_endpoint_damping
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p,p∈P j → p.Prime) (Vmass : J → ℝ)
    (pads : ℕ) (Z : Finset (ℤ×ℤ)) (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q : ℝ) (α β : ℕ → ℂ) :
    let f := fun s : MarkedPhysicalState P (pads+1) Z =>
      markedPhysicalEndpointVector P (pads+1) α β s.1.1.1
    markedPhysicalEdgePairing P hP Vmass pads Z hZ ψ η d₀ Y Q q f f =
      markedPhysicalEdgePairing P hP Vmass pads Z hZ ψ η d₀ Y Q 1 f f := by
  dsimp only
  let f := fun s : MarkedPhysicalState P (pads+1) Z =>
    markedPhysicalEndpointVector P (pads+1) α β s.1.1.1
  change markedPhysicalEdgePairing P hP Vmass pads Z hZ ψ η d₀ Y Q q f f =
    markedPhysicalEdgePairing P hP Vmass pads Z hZ ψ η d₀ Y Q 1 f f
  rw [markedPhysicalEdgePairing_eq_delta_sub_major P hP Vmass pads Z hZ ψ η d₀ Y Q q f f,
    markedPhysicalEdgePairing_eq_delta_sub_major P hP Vmass pads Z hZ ψ η d₀ Y Q 1 f f,
    markedPhysicalEdgeDetectorPairing_endpoint_damping P hP Vmass pads Z hZ η d₀ Y q
      (markedRawEdgeDeltaDetector ψ Y) α β,
    markedPhysicalEdgeDetectorPairing_endpoint_damping P hP Vmass pads Z hZ η d₀ Y q
      (markedRawEdgeMajorDetector ψ Q Y) α β]

theorem markedPhysicalTypeIIPairing_eq_q_one
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x : ℝ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q q U V : ℝ) (Sα Sβ : Finset ℕ) (modulation : ℝ) (β : ℕ → ℂ) :
    markedPhysicalTypeIIPairing e x ψ η d₀ Y Q q U V Sα Sβ modulation β =
      markedPhysicalTypeIIPairing e x ψ η d₀ Y Q 1 U V Sα Sβ modulation β :=
  markedPhysicalEdgePairing_endpoint_damping (fun j => markedLogPowerBand (e j) x)
    (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1)
    (fun j => bandReciprocalMass (markedLogPowerBand (e j) x))
    ⌊(Real.log x)^(1/100:ℝ)⌋₊ (markedPhysicalPrimitiveBox U (16*U) V (2*V))
    (fun _ hz => (Finset.mem_filter.mp hz).2) ψ η d₀ Y Q q
    (markedMajorRestrictedCoefficient (Real.exp ((Real.log x)^(6/25:ℝ))) modulation Sα)
    (markedPhysicalRestrictedBeta Sβ β)

theorem markedPhysicalTypeIICharacterPairing_eq_q_one
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x : ℝ) (Mχ : ℕ) (ξ : DirichletCharacter ℂ Mχ)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q q U V : ℝ) (Sα Sβ : Finset ℕ) (modulation : ℝ) (β : ℕ → ℂ) :
    markedPhysicalTypeIICharacterPairing e x Mχ ξ ψ η d₀ Y Q q U V Sα Sβ modulation β =
      markedPhysicalTypeIICharacterPairing e x Mχ ξ ψ η d₀ Y Q 1 U V Sα Sβ modulation β :=
  markedPhysicalEdgePairing_endpoint_damping (fun j => markedLogPowerBand (e j) x)
    (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1)
    (fun j => bandReciprocalMass (markedLogPowerBand (e j) x))
    ⌊(Real.log x)^(1/100:ℝ)⌋₊ (markedPhysicalPrimitiveBox U (16*U) V (2*V))
    (fun _ hz => (Finset.mem_filter.mp hz).2) ψ η d₀ Y Q q
    (fun n => ξ n*markedMajorRestrictedCoefficient (Real.exp ((Real.log x)^(6/25:ℝ))) modulation Sα n)
    (fun n => ξ n*markedPhysicalRestrictedBeta Sβ β n)

end
end ArtinMatthews
