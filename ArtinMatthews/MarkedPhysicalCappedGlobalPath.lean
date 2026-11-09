module

public import ArtinMatthews.MarkedPhysicalCappedPathTerm
public import ArtinMatthews.MarkedPhysicalCoordinateLineGlobal


set_option backward.privateInPublic true
@[expose] public section

/-! The actual Boundary coordinate capped main term on the path/order
carrier. Both support implications are discharged from the literal term;
the full-band baseline is retained explicitly. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] [decJ : DecidableEq J]
  (e : J → ℝ) (x : ℝ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
  (d₀ Y Q q U Vr : ℝ) (R : ℕ) (hR : 1≤R)
  (z₀ : ↥(markedPrimitiveCoordinateTube R)) (hz₀ : z₀.1=(1,0))
  (hZ : ∀ z∈markedPrimitiveCoordinateTube R,IsCoprime z.1 z.2)

local notation "PN" => (fun j => markedLogPowerBand (e j) x)
local notation "hP" => (fun _ _ hp => And.left (mem_markedLogPowerBand.mp hp))
local notation "Vactual" => (fun j => bandReciprocalMass (markedLogPowerBand (e j) x))
local notation "pads" => ⌊(Real.log x)^(1/100:ℝ)⌋₊
local notation "N" => markedMemoryMomentLength x

set_option backward.isDefEq.respectTransparency false in
include hz₀ in
theorem markedPhysicalCoordinateCappedGlobal_path :
    markedPhysicalCoordinateCappedGlobal e x ψ η d₀ Y Q q U Vr R hR=
      ((∏ j,∏ p : markedRawActualPrimeBand e x j,markedMemoryBaseline q N p.1:ℝ):ℂ)*
      ((markedPhysicalMass Vactual (markedPadSlots x):ℂ)*
        ∑ d : {d : MarkedMemoryActivePathData (markedRawActualPrimeBand e x) pads
          (markedPrimitiveCoordinateTube R) N // d.position 0=z₀},
          (markedMemoryPathCappedChoiceSum hZ d.1 q (markedDirtyMemoryCutoff x):ℂ)*
            ∑ order : Fin N → J → Equiv.Perm (Fin pads),
              markedPhysicalCoordinateIndexCoefficient PN hP Vactual pads ψ η d₀ Y Q
                (markedPhysicalActivePathIndex PN hP d.1 order)*
              (markedPhysicalCoordinateIndexGoodVolume e x d₀ Y U Vr
                (markedPhysicalActivePathIndex PN hP d.1 order) hR:ℂ)*
              if d.1.position (Fin.last N)=z₀ then 1 else 0) := by
  cases Subsingleton.elim decJ (Classical.decEq J)
  let F := fun i : MarkedPhysicalCoordinateIndex PN (pads+1) N R =>
    markedPhysicalCoordinateCappedTerm e x Vactual ψ η d₀ Y Q i hR q U Vr (markedDirtyMemoryCutoff x)
  have hbad (i : MarkedPhysicalCoordinateIndex PN (pads+1) N R)
      (hi : ¬∀ v,MarkedPhysicalMarkingDistinct (i.1 v)) : F i=0 := by
    unfold F markedPhysicalCoordinateCappedTerm markedPhysicalCoordinatePathApply
    dsimp only [markedPadSlots,markedRawActualPrimeBand] at *
    rw [dite_eq_right hi]
  have hzero (i : MarkedPhysicalCoordinateIndex PN (pads+1) N R)
      (hi : markedPhysicalCoordinateIndexCoefficient PN hP Vactual pads ψ η d₀ Y Q i=0) : F i=0 := by
    unfold F markedPhysicalCoordinateCappedTerm markedPhysicalCoordinatePathApply
    dsimp only [markedPadSlots,markedRawActualPrimeBand] at *
    by_cases ha : ∀ v,MarkedPhysicalMarkingDistinct (i.1 v)
    · rw [dite_eq_left ha,dite_eq_right (fun hc => hc hi)]
    · rw [dite_eq_right ha]
  have hs := markedPhysicalInitialPathIndex_sum PN hP Vactual ψ η d₀ Y Q z₀ hz₀ hR F hbad hzero
  have ht : (∑ i : MarkedPhysicalCoordinateIndex PN (pads+1) N R,F i)=
      ((∏ j,∏ p : markedRawActualPrimeBand e x j,markedMemoryBaseline q N p.1:ℝ):ℂ)*
        ∑ d : {d : MarkedMemoryActivePathData (markedRawActualPrimeBand e x) pads
          (markedPrimitiveCoordinateTube R) N // d.position 0=z₀},
          (markedMemoryPathCappedChoiceSum hZ d.1 q (markedDirtyMemoryCutoff x):ℂ)*
            ∑ order : Fin N → J → Equiv.Perm (Fin pads),
              markedPhysicalCoordinateIndexCoefficient PN hP Vactual pads ψ η d₀ Y Q
                (markedPhysicalActivePathIndex PN hP d.1 order)*
              (markedPhysicalCoordinateIndexGoodVolume e x d₀ Y U Vr
                (markedPhysicalActivePathIndex PN hP d.1 order) hR:ℂ)*
              if d.1.position (Fin.last N)=z₀ then 1 else 0 := by
    apply hs.trans
    rw [Fintype.sum_sigma,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    rw [Finset.mul_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro order _
    have hh := markedPhysicalCoordinateCappedTerm_path e x Vactual ψ η d₀ Y Q q U Vr hR hZ z₀ hz₀ d.1 d.2 order
      (markedDirtyMemoryCutoff x)
    dsimp only [markedPhysicalInitialPathIndex,F]
    rw [hh]
    ring
  unfold markedPhysicalCoordinateCappedGlobal
  dsimp only [markedPadSlots,markedRawActualPrimeBand]
  change (markedPhysicalMass Vactual (markedPadSlots x):ℂ)*(∑ i,F i)=_
  rw [ht]
  exact mul_left_comm _ _ _

end
end ArtinMatthews
