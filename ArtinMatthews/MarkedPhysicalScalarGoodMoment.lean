module

public import ArtinMatthews.MarkedPhysicalTypeIIGoodPairing


set_option backward.privateInPublic true
@[expose] public section

/-! The physical good pairing for arbitrary bounded scalar coefficients.
The localized moment is the literal growing moment from the fixed-coefficient proof. -/
namespace ArtinMatthews
open scoped BigOperators Classical
noncomputable section
attribute [local instance] markedPhysicalMomentFintype markedPhysicalMomentDecidableEq

variable {J : Type*} [Fintype J] [DecidableEq J]

/-- Exact physical pairing of the two scalar endpoint vectors. -/
def markedPhysicalScalarPairing
    (e : J → ℝ) (x : ℝ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q q U V : ℝ) (α β : ℕ → ℂ) : ℂ :=
  let P := fun j => markedLogPowerBand (e j) x
  let f := fun s : MarkedPhysicalState P (markedPadSlots x)
      (markedPhysicalPrimitiveBox U (16*U) V (2*V)) =>
    markedPhysicalEndpointVector P (markedPadSlots x) α β s.1.1.1
  markedPhysicalEdgePairing P (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1)
    (fun j => bandReciprocalMass (P j)) ⌊(Real.log x)^(1/100:ℝ)⌋₊
    (markedPhysicalPrimitiveBox U (16*U) V (2*V))
    (fun _ hz => (Finset.mem_filter.mp hz).2) ψ η d₀ Y Q q f f

/-- The identical pairing after both actual endpoint masks. -/
def markedPhysicalScalarGoodPairing
    (e : J → ℝ) (x : ℝ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q q U V : ℝ) (w : ↥(markedPhysicalPrimitiveBox U (16*U) V (2*V)) → ℤ × ℤ)
    (α β : ℕ → ℂ) : ℂ :=
  let P := fun j => markedLogPowerBand (e j) x
  let f := markedPhysicalGoodVector (MarkedPhysicalActualGood e x d₀ Y w)
    (fun s => markedPhysicalEndpointVector P (markedPadSlots x) α β s.1.1.1)
  markedPhysicalEdgePairing P (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1)
    (fun j => bandReciprocalMass (P j)) ⌊(Real.log x)^(1/100:ℝ)⌋₊
    (markedPhysicalPrimitiveBox U (16*U) V (2*V))
    (fun _ hz => (Finset.mem_filter.mp hz).2) ψ η d₀ Y Q q f f

theorem markedPhysicalScalarGoodPairing_moment_bound
    (e : J → ℝ) (x : ℝ) (hx : 1 < x)
    (hdis : Pairwise (fun i j => Disjoint (markedLogPowerBand (e i) x) (markedLogPowerBand (e j) x)))
    (hVmass : ∀ j,0 < bandReciprocalMass (markedLogPowerBand (e j) x))
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q K U V Cα Cβ G : ℝ)
    (hd₀ : 0 < d₀) (hY : 0 < Y) (hK : 0 ≤ K) (hU : 0 < U) (hV : 0 < V)
    (hψ : Function.support ψ ⊆ Set.Icc (-K) K)
    (w : ↥(markedPhysicalPrimitiveBox U (16*U) V (2*V)) → ℤ × ℤ)
    (α β : ℕ → ℂ)
    (hα : ∀ n, ‖α n‖ ≤ (Real.log x)^Cα) (hβ : ∀ n, ‖β n‖ ≤ (Real.log x)^Cβ)
    (hMoment : markedPhysicalActualPositionMoment e x ψ η d₀ Y Q q U V w ≤
      (U*V)*(Real.log x)^(-G*(markedMemoryMomentLength x:ℝ))) :
    ‖markedPhysicalScalarGoodPairing e x ψ η d₀ Y Q q U V w α β‖ ≤
      32*Real.sqrt (2*(⌈2*K+1⌉₊:ℝ)+1)*(256*(d₀*Y)+1)^((markedMemoryMomentLength x:ℝ)⁻¹)*
        (U*V)*(Real.log x)^(2*(Cα+Cβ)-G) := by
  let P := fun j => markedLogPowerBand (e j) x
  let hP := fun j p (hp : p∈P j) => (mem_markedLogPowerBand.mp hp).1
  let Vmass := fun j => bandReciprocalMass (P j)
  let pads := ⌊(Real.log x)^(1/100:ℝ)⌋₊
  let Z := markedPhysicalPrimitiveBox U (16*U) V (2*V)
  have hZ : ∀ z∈Z,IsCoprime z.1 z.2 := fun _ hz => (Finset.mem_filter.mp hz).2
  let Good := MarkedPhysicalActualGood e x d₀ Y w
  let a : Z → ℂ := fun z => markedPhysicalEndpointVector P (pads+1) α β z.1
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
    have heq : markedPhysicalPositionMoment P (pads+1) Z Vmass A (k+1) =
        markedPhysicalActualPositionMoment e x ψ η d₀ Y Q q U V w := by
      rw [hk]
      rfl
    rw [heq,← hN]
    exact hMoment
  have hbox (z : ℤ × ℤ) (hz : z∈Z) : U ≤ (z.1:ℝ) ∧ (z.1:ℝ) ≤ 16*U ∧
      V ≤ (z.2:ℝ) ∧ (z.2:ℝ) ≤ 2*V := by
    have hz' := Finset.mem_product.mp (Finset.mem_filter.mp hz).1
    obtain ⟨hu₁, hu₂⟩ := (fixedURoot_mem_closed_interval U (16*U) z.1).mp hz'.1
    obtain ⟨hv₁, hv₂⟩ := (fixedURoot_mem_closed_interval V (2*V) z.2).mp hz'.2
    exact ⟨hu₁,hu₂,hv₁,hv₂⟩
  let C := Cα+Cβ-2
  let L := Real.log x
  have hL : 0 < L := Real.log_pos hx
  have hpow : (L^Cα*L^Cβ)^2=L^(2*C+4) := by
    rw [← Real.rpow_add hL Cα Cβ,pow_two,← Real.rpow_add hL]
    congr 1
    dsimp only [C]
    ring
  have hα₀ : 0 ≤ L^Cα := Real.rpow_nonneg hL.le _
  have hβ₀ : 0 ≤ L^Cβ := Real.rpow_nonneg hL.le _
  have hsup (z : Z) : ‖a z‖^2 ≤ L^(2*C+4) := by
    rw [← hpow]
    exact pow_le_pow_left₀ (norm_nonneg _)
      (markedPhysicalEndpointVector_norm_le_global P (pads+1) α β hα₀ hβ₀ hα hβ z.val) 2
  have hE : (∑ s : MarkedPhysicalState P (pads+1) Z,
      markedPhysicalMass Vmass (pads+1)*‖a s.1.1‖^2) ≤ 32*(U*V)*L^(2*C+4) := by
    rw [← hpow, ← mul_assoc]
    exact markedPhysicalEndpointEnergy_box P hP hdis (pads+1) Z hVmass hU hV hbox
      α β hα₀ hβ₀ (fun n _ => hα n) (fun n _ => hβ n)
  have hp := markedPhysicalGoodPairing_of_moment_bound P hP Vmass hVmass pads Z hZ ψ η
    d₀ Y Q q K U V L C G Good (fun σ s => markedPhysicalActualGood_slots e x d₀ Y w σ s)
    hd₀ hY hK hU hV hL hψ (fun z hz => ⟨(hbox z hz).1,(hbox z hz).2.1⟩)
    a a k hsup hE hE hT
  have he : 2*C+4-G=2*(Cα+Cβ)-G := by dsimp only [C]; ring
  rw [← hN, he] at hp
  exact hp

end
end ArtinMatthews
