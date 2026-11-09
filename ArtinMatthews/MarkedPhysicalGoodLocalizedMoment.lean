module

public import ArtinMatthews.MarkedPhysicalLocalizedMoment
public import ArtinMatthews.MarkedPhysicalMatrixPairing
public import ArtinMatthews.MarkedLocalizedMomentRoots


set_option backward.privateInPublic true
@[expose] public section

/-! The localized moment bound for the original, good physical pairing.
The high moment is the genuine constant-mass GSTSG moment, retained
explicitly for the separate arithmetic word transfer. -/
namespace ArtinMatthews
open Matrix
open scoped BigOperators Classical ComplexOrder
noncomputable section
attribute [local instance] markedPhysicalMomentFintype markedPhysicalMomentDecidableEq

theorem markedPhysicalGoodPairing_localized_moment
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p,p∈P j → p.Prime) (V : J → ℝ) (hV : ∀ j,0<V j)
    (pads : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q K U : ℝ)
    (G : MarkedPhysicalState P (pads+1) Z → Prop)
    (hG : ∀ σ s,G (markedPhysicalSlotEquiv P (pads+1) Z σ s) ↔ G s)
    (hd₀ : 0<d₀) (hY : 0<Y) (hK : 0≤K) (hU : 0<U)
    (hψ : Function.support ψ ⊆ Set.Icc (-K) K)
    (hfirst : ∀ z∈Z,U≤(z.1:ℝ) ∧ (z.1:ℝ)≤16*U)
    (a b : Z → ℂ) (M : ℝ) (hM : 0≤M) (ha : ∀ z,‖a z‖^2≤M) (k : ℕ) :
    let A := markedPhysicalRestrictedMatrix P hP V pads Z hZ ψ η d₀ Y Q q G
    let E := fun v : Z → ℂ => ∑ s : MarkedPhysicalState P (pads+1) Z,
      markedPhysicalMass V (pads+1)*‖v s.1.1‖^2
    ‖markedPhysicalEdgePairing P hP V pads Z hZ ψ η d₀ Y Q q
        (markedPhysicalGoodVector G (fun s => a s.1.1))
        (markedPhysicalGoodVector G (fun s => b s.1.1))‖^(2*(k+1)) ≤
      (2*(⌈2*K+1⌉₊:ℝ)+1)^(k+1) * (E b)^(k+1) * (E a)^k *
        ((256*(d₀*Y)+1)*M) * markedPhysicalPositionMoment P (pads+1) Z V A (k+1) := by
  dsimp only
  have h := markedPhysicalRestrictedMatrix_localized_moment P hP V pads Z hZ ψ η d₀ Y Q q K U G
    hd₀ hY hK hU hψ hfirst a
    (markedPositionLift (fun s : MarkedPhysicalState P (pads+1) Z => s.1.1)
      (markedPhysicalMass V (pads+1)) b) M hM ha k
  dsimp only at h
  rw [markedPhysicalRestrictedMatrix_pairing P hP V hV pads Z hZ ψ η d₀ Y Q q G hG a b,
    markedPositionLift_energy _ _ (markedPhysicalMass_pos V (pads+1) hV).le b,
    markedPositionLift_energy _ _ (markedPhysicalMass_pos V (pads+1) hV).le a] at h
  exact h

theorem markedPhysicalActualGoodPairing_localized_moment
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x : ℝ) (V : J → ℝ) (hV : ∀ j,0<V j)
    (Z : Finset (ℤ × ℤ)) (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q K U : ℝ)
    (w : Z → ℤ × ℤ)
    (hd₀ : 0<d₀) (hY : 0<Y) (hK : 0≤K) (hU : 0<U)
    (hψ : Function.support ψ ⊆ Set.Icc (-K) K)
    (hfirst : ∀ z∈Z,U≤(z.1:ℝ) ∧ (z.1:ℝ)≤16*U)
    (a b : Z → ℂ) (M : ℝ) (hM : 0≤M) (ha : ∀ z,‖a z‖^2≤M) (k : ℕ) :
    let P := fun j => markedLogPowerBand (e j) x
    let hP := fun j p (hp : p∈P j) => (mem_markedLogPowerBand.mp hp).1
    let pads := ⌊(Real.log x)^(1/100:ℝ)⌋₊
    let G := MarkedPhysicalActualGood e x d₀ Y w
    let A := markedPhysicalRestrictedMatrix P hP V pads Z hZ ψ η d₀ Y Q q G
    let E := fun v : Z → ℂ => ∑ s : MarkedPhysicalState P (markedPadSlots x) Z,
      markedPhysicalMass V (markedPadSlots x)*‖v s.1.1‖^2
    ‖markedPhysicalEdgePairing P hP V pads Z hZ ψ η d₀ Y Q q
        (markedPhysicalGoodVector G (fun s => a s.1.1))
        (markedPhysicalGoodVector G (fun s => b s.1.1))‖^(2*(k+1)) ≤
      (2*(⌈2*K+1⌉₊:ℝ)+1)^(k+1) * (E b)^(k+1) * (E a)^k *
        ((256*(d₀*Y)+1)*M) * markedPhysicalPositionMoment P (markedPadSlots x) Z V A (k+1) := by
  exact markedPhysicalGoodPairing_localized_moment
    (fun j => markedLogPowerBand (e j) x) (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1)
    V hV ⌊(Real.log x)^(1/100:ℝ)⌋₊ Z hZ ψ η d₀ Y Q q K U
    (MarkedPhysicalActualGood e x d₀ Y w)
    (fun σ s => markedPhysicalActualGood_slots e x d₀ Y w σ s)
    hd₀ hY hK hU hψ hfirst a b M hM ha k

theorem markedPhysicalGoodPairing_localized_root
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p,p∈P j → p.Prime) (V : J → ℝ) (hV : ∀ j,0<V j)
    (pads : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q K U : ℝ)
    (G : MarkedPhysicalState P (pads+1) Z → Prop)
    (hG : ∀ σ s,G (markedPhysicalSlotEquiv P (pads+1) Z σ s) ↔ G s)
    (hd₀ : 0<d₀) (hY : 0<Y) (hK : 0≤K) (hU : 0<U)
    (hψ : Function.support ψ ⊆ Set.Icc (-K) K)
    (hfirst : ∀ z∈Z,U≤(z.1:ℝ) ∧ (z.1:ℝ)≤16*U)
    (a b : Z → ℂ) (M : ℝ) (hM : 0≤M) (ha : ∀ z,‖a z‖^2≤M) (k : ℕ) :
    let A := markedPhysicalRestrictedMatrix P hP V pads Z hZ ψ η d₀ Y Q q G
    let E := fun v : Z → ℂ => ∑ s : MarkedPhysicalState P (pads+1) Z,
      markedPhysicalMass V (pads+1)*‖v s.1.1‖^2
    ‖markedPhysicalEdgePairing P hP V pads Z hZ ψ η d₀ Y Q q
        (markedPhysicalGoodVector G (fun s => a s.1.1))
        (markedPhysicalGoodVector G (fun s => b s.1.1))‖ ≤
      Real.sqrt (2*(⌈2*K+1⌉₊:ℝ)+1) * Real.sqrt (E b) *
        (E a)^((k:ℝ)/(2*((k+1:ℕ):ℝ))) *
          ((256*(d₀*Y)+1)*M)^((2*((k+1:ℕ):ℝ))⁻¹) *
            (markedPhysicalPositionMoment P (pads+1) Z V A (k+1))^((2*((k+1:ℕ):ℝ))⁻¹) := by
  dsimp only
  have hp := markedPhysicalGoodPairing_localized_moment P hP V hV pads Z hZ ψ η d₀ Y Q q K U G hG
    hd₀ hY hK hU hψ hfirst a b M hM ha k
  dsimp only at hp
  have he (v : Z → ℂ) : 0≤∑ s : MarkedPhysicalState P (pads+1) Z,
      markedPhysicalMass V (pads+1)*‖v s.1.1‖^2 :=
    Finset.sum_nonneg (fun _ _ => mul_nonneg (markedPhysicalMass_pos V (pads+1) hV).le (sq_nonneg _))
  exact markedLocalizedMoment_root_bound _ _ _ _ _ _ (norm_nonneg _) (by positivity)
    (he b) (he a) (mul_nonneg (by positivity) hM)
    (markedPhysicalPositionMoment_nonneg P (pads+1) Z V _ (k+1)) k hp

end
end ArtinMatthews
