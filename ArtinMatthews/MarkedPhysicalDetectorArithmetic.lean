module

public import ArtinMatthews.MarkedPhysicalDetectorKernel


set_option backward.privateInPublic true
@[expose] public section

/-! A pure arithmetic expression for the actual physical detector. This
keeps the state-to-label transports outside all dependent if expressions. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.propDecidable

def markedPhysicalDetectorArithmetic (η : ℝ → ℂ) (d₀ Y : ℝ)
    (detector : ℤ → ℤ → ℤ → ℂ) (D b a : ℕ) (t : ℤ) (ban : Prop) : ℂ :=
  if d₀≤(D:ℝ) ∧ (D:ℝ)<2*d₀ then
    if (D:ℤ) ∣ t then if ban then 0 else
      ((d₀/(D:ℝ):ℝ):ℂ)*η ((b:ℝ)/Y)*η ((a:ℝ)/Y)*detector b a (t/(D:ℤ))
    else 0 else 0

theorem markedPhysicalEdgeDetectorCoefficient_arithmetic
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p,p ∈ P j → p.Prime) (V : J → ℝ)
    (pads : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (η : ℝ → ℂ) (d₀ Y : ℝ) (detector : ℤ → ℤ → ℤ → ℂ)
    (s t : MarkedPhysicalState P (pads+1) Z) :
    markedPhysicalEdgeDetectorCoefficient P hP V pads Z hZ η d₀ Y 1 detector s t=
      (markedPhysicalMass V (pads+2):ℂ)*
        (if ((markedRawActiveSplit pads) (markedPhysicalStateToRaw P hP (pads+1) Z s).2.1).1=
            ((markedRawActiveSplit pads) (markedPhysicalStateToRaw P hP (pads+1) Z t).2.1).1 then
          markedPhysicalDetectorArithmetic η d₀ Y detector
            (markedRawCopiedProduct ((markedRawActiveSplit pads) (markedPhysicalStateToRaw P hP (pads+1) Z s).2.1).1)
            (markedRawLastProduct ((markedRawActiveSplit pads) (markedPhysicalStateToRaw P hP (pads+1) Z s).2.1).2)
            (markedRawLastProduct ((markedRawActiveSplit pads) (markedPhysicalStateToRaw P hP (pads+1) Z t).2.1).2)
            (markedMinorIntegerDet s.1.1.1 t.1.1.1)
            (MarkedRawFullCrossBan (markedPhysicalStateToRaw P hP (pads+1) Z s).2.1
              ((markedRawActiveSplit pads) (markedPhysicalStateToRaw P hP (pads+1) Z t).2.1).2)
        else 0) := by
  rw [markedPhysicalEdgeDetectorCoefficient_kernel]
  simp only [markedPhysicalEndpointDamping,Real.one_rpow,Complex.ofReal_one,one_mul,mul_one]
  rfl

end
end ArtinMatthews
