module

public import ArtinMatthews.MarkedPhysicalGoodPairing
public import ArtinMatthews.MarkedMinorArcBanAdjoint


set_option backward.privateInPublic true
@[expose] public section

/-! The exact original physical edge coefficient in raw-minus-major kernel
form. Both physical dampings, the copied-prefix test and full cross ban are
retained, with the original joint label normalization. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem markedPhysicalRawEndpointFactor_one
    {J : Type*} [Fintype J] (P : J → Finset ℕ)
    (hP : ∀ j p,p ∈ P j → p.Prime) (M : ℕ)
    (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (s : MarkedPhysicalState P M Z) :
    markedRawEndpointFactor hZ 1 (fun _ => 1) (markedPhysicalStateToRaw P hP M Z s) = 1 := by
  simp [markedRawEndpointFactor,markedPhysicalStateToRaw_distinct P hP M Z s]

theorem markedPhysicalRawJointCoefficient_kernel
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p,p ∈ P j → p.Prime) (pads : ℕ)
    (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q : ℝ)
    (s t : MarkedPhysicalState P (pads+1) Z) :
    let u := markedPhysicalStateToRaw P hP (pads+1) Z s
    let v := markedPhysicalStateToRaw P hP (pads+1) Z t
    let b := ((markedRawActiveSplit pads) u.2.1).2
    let a := ((markedRawActiveSplit pads) v.2.1).2
    let D := markedRawCopiedProduct ((markedRawActiveSplit pads) u.2.1).1
    markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q 1 (fun _ => 1) u v =
      if d₀ ≤ (D : ℝ) ∧ (D : ℝ) < 2*d₀ then
        if (D : ℤ) ∣ markedMinorIntegerDet s.1.1.1 t.1.1.1 then
          if MarkedRawFullCrossBan u.2.1 a then 0 else
            ((d₀/(D : ℝ) : ℝ) : ℂ) * η ((markedRawLastProduct b : ℝ)/Y) *
              η ((markedRawLastProduct a : ℝ)/Y) *
              markedBanEdgeKernel ψ Q Y (markedRawLastProduct b) (markedRawLastProduct a)
                (markedMinorIntegerDet s.1.1.1 t.1.1.1/(D : ℤ))
        else 0 else 0 := by
  dsimp only
  unfold markedRawEdgeJointCoefficient
  dsimp only
  rw [markedPhysicalRawEndpointFactor_one P hP (pads+1) Z hZ s,
    markedPhysicalRawEndpointFactor_one P hP (pads+1) Z hZ t]
  simp only [mul_one]
  dsimp only [markedPhysicalStateToRaw]
  have he (l b a : ℤ) : l-b+a=0 ↔ l=b-a := by omega
  simp only [markedBan_minor_integral,markedBanEdgeKernel,he,mul_assoc]

theorem markedPhysicalEdgeCoefficient_kernel
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p,p ∈ P j → p.Prime) (V : J → ℝ)
    (pads : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q : ℝ)
    (s t : MarkedPhysicalState P (pads+1) Z) :
    let u := markedPhysicalStateToRaw P hP (pads+1) Z s
    let v := markedPhysicalStateToRaw P hP (pads+1) Z t
    let b := ((markedRawActiveSplit pads) u.2.1).2
    let a := ((markedRawActiveSplit pads) v.2.1).2
    let D := markedRawCopiedProduct ((markedRawActiveSplit pads) u.2.1).1
    markedPhysicalEdgeCoefficient P hP V pads Z hZ ψ η d₀ Y Q q s t =
      (markedPhysicalMass V (pads+2) : ℂ) *
        (if ((markedRawActiveSplit pads) u.2.1).1 = ((markedRawActiveSplit pads) v.2.1).1 then
          (markedPhysicalEndpointDamping P (pads+1) q s.1.1.1 : ℂ) *
            (if d₀ ≤ (D : ℝ) ∧ (D : ℝ) < 2*d₀ then
              if (D : ℤ) ∣ markedMinorIntegerDet s.1.1.1 t.1.1.1 then
                if MarkedRawFullCrossBan u.2.1 a then 0 else
                  ((d₀/(D : ℝ) : ℝ) : ℂ) * η ((markedRawLastProduct b : ℝ)/Y) *
                    η ((markedRawLastProduct a : ℝ)/Y) *
                    markedBanEdgeKernel ψ Q Y (markedRawLastProduct b) (markedRawLastProduct a)
                      (markedMinorIntegerDet s.1.1.1 t.1.1.1/(D : ℤ))
              else 0 else 0) *
            (markedPhysicalEndpointDamping P (pads+1) q t.1.1.1 : ℂ)
        else 0) := by
  dsimp only
  unfold markedPhysicalEdgeCoefficient
  dsimp only
  rw [markedPhysicalRawJointCoefficient_kernel P hP pads Z hZ ψ η d₀ Y Q s t,
    markedPhysicalMass_edge]

end ArtinMatthews
