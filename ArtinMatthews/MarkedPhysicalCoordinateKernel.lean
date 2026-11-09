module

public import ArtinMatthews.MarkedPhysicalRawMatrixEntry
public import ArtinMatthews.MarkedPhysicalEdgeKernelFormula
public import ArtinMatthews.MarkedRawGoodRootTransport


set_option backward.privateInPublic true
@[expose] public section

/-! The original physical complex edge weight at a fixed coordinate path
and ordered labels. Its entire archimedean kernel is root-independent;
the separate arithmetic q-hit factors are retained literally. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def markedPhysicalCoordinateKernel {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (V : J → ℝ) (pads : ℕ)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q : ℝ)
    (source target : MarkedRawActive P (pads+1)) (z z' : ℤ × ℤ) : ℂ :=
  let b := ((markedRawActiveSplit pads) source).2
  let a := ((markedRawActiveSplit pads) target).2
  let D := markedRawCopiedProduct ((markedRawActiveSplit pads) source).1
  ((∏ j,(V j)⁻¹:ℝ):ℂ) *
    (if ((markedRawActiveSplit pads) source).1=((markedRawActiveSplit pads) target).1 then
      if d₀ ≤ (D:ℝ) ∧ (D:ℝ)<2*d₀ then
        if (D:ℤ) ∣ markedMinorIntegerDet z z' then
          if MarkedRawFullCrossBan source a then 0 else
            ((d₀/(D:ℝ):ℝ):ℂ)*η ((markedRawLastProduct b:ℝ)/Y)*η ((markedRawLastProduct a:ℝ)/Y)*
              markedBanEdgeKernel ψ Q Y (markedRawLastProduct b) (markedRawLastProduct a)
                (markedMinorIntegerDet z z'/(D:ℤ))
        else 0 else 0
    else 0)

theorem markedPhysicalEdgeMatrix_coordinate_kernel
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p,p∈P j → p.Prime)
    (V : J → ℝ) (hV : ∀ j,0<V j) (pads : ℕ)
    (Z : Finset (ℤ × ℤ)) (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q : ℝ)
    (s t : MarkedPhysicalState P (pads+1) Z) (root completion z z' : ℤ × ℤ)
    (hdet : markedMinorIntegerDet root completion=1)
    (hs : s.1.1.1=markedPhysicalRootLift root completion z)
    (ht : t.1.1.1=markedPhysicalRootLift root completion z') :
    markedPhysicalEdgeMatrix P hP V pads Z hZ ψ η d₀ Y Q q s t =
      (markedPhysicalEndpointDamping P (pads+1) q s.1.1.1:ℂ)*
        markedPhysicalCoordinateKernel V pads ψ η d₀ Y Q
          (markedPhysicalStateToRaw P hP (pads+1) Z s).2.1
          (markedPhysicalStateToRaw P hP (pads+1) Z t).2.1 z z' *
        (markedPhysicalEndpointDamping P (pads+1) q t.1.1.1:ℂ) := by
  rw [markedPhysicalEdgeMatrix_eq_raw P hP V hV pads Z hZ ψ η d₀ Y Q q s t]
  rw [markedPhysicalRawJointCoefficient_kernel P hP pads Z hZ ψ η d₀ Y Q s t]
  rw [hs,ht,markedPhysicalRootLift_det root completion z z' hdet]
  unfold markedPhysicalCoordinateKernel
  split_ifs <;> simp_all
  all_goals ring

theorem markedPhysicalCoordinateKernel_root_lift
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (V : J → ℝ) (pads : ℕ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q : ℝ)
    (source target : MarkedRawActive P (pads+1)) (root completion z z' : ℤ × ℤ)
    (hdet : markedMinorIntegerDet root completion=1) :
    markedPhysicalCoordinateKernel V pads ψ η d₀ Y Q source target
      (markedPhysicalRootLift root completion z) (markedPhysicalRootLift root completion z') =
      markedPhysicalCoordinateKernel V pads ψ η d₀ Y Q source target z z' := by
  unfold markedPhysicalCoordinateKernel
  rw [markedPhysicalRootLift_det root completion z z' hdet]

end ArtinMatthews
