module

public import ArtinMatthews.MarkedPhysicalTypeIILocalized
public import ArtinMatthews.MarkedPhysicalTypeIIEndpointBounds


set_option backward.privateInPublic true
@[expose] public section

/-! The literal good minor pairing for the original centered Type II
alpha and supported beta. Its moment criterion keeps every source
normalizer and the exact growing moment length. -/
namespace ArtinMatthews
open scoped BigOperators Classical
noncomputable section
attribute [local instance] markedPhysicalMomentFintype markedPhysicalMomentDecidableEq

def markedPhysicalTypeIIGoodPairing {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x : ℝ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q q U V : ℝ)
    (w : ↥(markedPhysicalPrimitiveBox U (16*U) V (2*V)) → ℤ × ℤ)
    (Sα Sβ : Finset ℕ) (modulation : ℝ) (β : ℕ → ℂ) : ℂ :=
  markedPhysicalEdgePairing (fun j => markedLogPowerBand (e j) x)
    (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1)
    (fun j => bandReciprocalMass (markedLogPowerBand (e j) x))
    ⌊(Real.log x)^(1/100:ℝ)⌋₊ (markedPhysicalPrimitiveBox U (16*U) V (2*V))
    (fun _ hz => (Finset.mem_filter.mp hz).2) ψ η d₀ Y Q q
    (markedPhysicalGoodVector (MarkedPhysicalActualGood e x d₀ Y w)
      (fun s => markedPhysicalTypeIIEndpoint e x Sα Sβ modulation β s.1.1.1))
    (markedPhysicalGoodVector (MarkedPhysicalActualGood e x d₀ Y w)
      (fun s => markedPhysicalTypeIIEndpoint e x Sα Sβ modulation β s.1.1.1))

theorem markedPhysicalTypeIIGoodPairing_moment_bound
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x : ℝ) (hx : 1 < x)
    (hVmass : ∀ j,0 < bandReciprocalMass (markedLogPowerBand (e j) x))
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q K U V C G : ℝ)
    (hd₀ : 0 < d₀) (hY : 0 < Y) (hK : 0 ≤ K) (hU : 0 < U) (hV : 0 < V)
    (hψ : Function.support ψ ⊆ Set.Icc (-K) K)
    (w : ↥(markedPhysicalPrimitiveBox U (16*U) V (2*V)) → ℤ × ℤ)
    (Sα Sβ : Finset ℕ) (modulation : ℝ) (β : ℕ → ℂ)
    (hsup : ∀ z,‖markedPhysicalTypeIIEndpoint e x Sα Sβ modulation β z‖^2 ≤
      (Real.log x)^(2*C+4))
    (hEnergy : markedPhysicalEndpointEnergy (fun j => markedLogPowerBand (e j) x) (markedPadSlots x)
      (markedPhysicalPrimitiveBox U (16*U) V (2*V))
      (fun j => bandReciprocalMass (markedLogPowerBand (e j) x))
      (markedMajorRestrictedCoefficient (Real.exp ((Real.log x)^(6/25:ℝ))) modulation Sα)
      (markedPhysicalRestrictedBeta Sβ β) ≤ 32*(U*V)*(Real.log x)^(2*C+4))
    (hMoment : markedPhysicalActualPositionMoment e x ψ η d₀ Y Q q U V w ≤
      (U*V)*(Real.log x)^(-G*(markedMemoryMomentLength x:ℝ))) :
    ‖markedPhysicalTypeIIGoodPairing e x ψ η d₀ Y Q q U V w Sα Sβ modulation β‖ ≤
      32*Real.sqrt (2*(⌈2*K+1⌉₊:ℝ)+1)*(256*(d₀*Y)+1)^((markedMemoryMomentLength x:ℝ)⁻¹)*
        (U*V)*(Real.log x)^(2*C+4-G) := by
  let P := fun j => markedLogPowerBand (e j) x
  let hP := fun j p (hp : p∈P j) => (mem_markedLogPowerBand.mp hp).1
  let Vmass := fun j => bandReciprocalMass (P j)
  let pads := ⌊(Real.log x)^(1/100:ℝ)⌋₊
  let Z := markedPhysicalPrimitiveBox U (16*U) V (2*V)
  have hZ : ∀ z∈Z,IsCoprime z.1 z.2 := fun _ hz => (Finset.mem_filter.mp hz).2
  let Good := MarkedPhysicalActualGood e x d₀ Y w
  let a : Z → ℂ := fun z => markedPhysicalTypeIIEndpoint e x Sα Sβ modulation β z.1
  let A := markedPhysicalRestrictedMatrix P hP Vmass pads Z hZ ψ η d₀ Y Q q Good
  let r := ⌈(Real.log x)^(1/2:ℝ)/2⌉₊
  have hr : 1 ≤ r := by
    have hn := markedPhysicalMomentLength_pos hx
    unfold markedMemoryMomentLength at hn
    dsimp [r]
    omega
  let k := r-1
  have hk : k+1=r := Nat.sub_add_cancel hr
  have hN : (markedMemoryMomentLength x:ℝ)=2*((k+1:ℕ):ℝ) := by
    rw [hk]
    simp only [markedMemoryMomentLength,Nat.cast_mul,Nat.cast_ofNat,r]
  have hT : markedPhysicalPositionMoment P (pads+1) Z Vmass A (k+1) ≤
      (U*V)*(Real.log x)^(-G*(2*((k+1:ℕ):ℝ))) := by
    have heq : markedPhysicalPositionMoment P (pads+1) Z Vmass A (k+1)=
        markedPhysicalActualPositionMoment e x ψ η d₀ Y Q q U V w := by
      rw [hk]
      rfl
    have ht := hMoment
    rw [hN] at ht
    exact heq.le.trans ht
  have hfirst (z : ℤ × ℤ) (hz : z∈Z) : U ≤ (z.1:ℝ) ∧ (z.1:ℝ) ≤ 16*U := by
    exact (fixedURoot_mem_closed_interval U (16*U) z.1).mp
      (Finset.mem_product.mp (Finset.mem_filter.mp hz).1).1
  have he : (∑ s : MarkedPhysicalState P (pads+1) Z,
      markedPhysicalMass Vmass (pads+1)*‖a s.1.1‖^2) ≤ 32*(U*V)*(Real.log x)^(2*C+4) := hEnergy
  have hp := markedPhysicalGoodPairing_of_moment_bound P hP Vmass hVmass pads Z hZ ψ η
    d₀ Y Q q K U V (Real.log x) C G Good
    (fun σ s => markedPhysicalActualGood_slots e x d₀ Y w σ s)
    hd₀ hY hK hU hV (Real.log_pos hx) hψ hfirst a a k (fun z => hsup z.1) he he hT
  rw [← hN] at hp
  exact hp

end
end ArtinMatthews
