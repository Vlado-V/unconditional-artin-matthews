module

public import ArtinMatthews.MarkedPhysicalActivePathReindex
public import ArtinMatthews.MarkedPhysicalCoordinateLineTerms


set_option backward.privateInPublic true
@[expose] public section

/-! The literal capped coordinate term on a canonical path. Its genuine
full-band baseline remains outside the signed capped choice sum; the
position loop and both copy probabilities are retained. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] [decJ : DecidableEq J]
  (e : J → ℝ) (x : ℝ) (V : J → ℝ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
  (d₀ Y Q q U Vr : ℝ) {n R : ℕ} (hR : 1≤R)
  (hZ : ∀ z∈markedPrimitiveCoordinateTube R,IsCoprime z.1 z.2)
  (z₀ : ↥(markedPrimitiveCoordinateTube R)) (hz₀ : z₀.1=(1,0))
  (d : MarkedMemoryActivePathData (fun j => markedRawPrimeBand (markedLogPowerBand (e j) x))
    ⌊(Real.log x)^(1/100:ℝ)⌋₊ (markedPrimitiveCoordinateTube R) n)
  (hd : d.position 0=z₀) (order : Fin n → J → Equiv.Perm (Fin ⌊(Real.log x)^(1/100:ℝ)⌋₊))

local notation "idx" => markedPhysicalActivePathIndex (fun j => markedLogPowerBand (e j) x)
  (fun _ _ hp => And.left (mem_markedLogPowerBand.mp hp)) d order

set_option backward.isDefEq.respectTransparency false in
include hd hz₀ in
theorem markedPhysicalCoordinateCappedTerm_path (cap : ℕ) :
    markedPhysicalCoordinateCappedTerm e x V ψ η d₀ Y Q idx hR q U Vr cap=
      ((∏ j,∏ p : markedRawActualPrimeBand e x j,markedMemoryBaseline q n p.1:ℝ):ℂ)*
      (markedMemoryPathCappedChoiceSum hZ d q cap:ℂ)*
      (markedPhysicalCoordinateIndexCoefficient (fun j => markedLogPowerBand (e j) x)
        (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) V ⌊(Real.log x)^(1/100:ℝ)⌋₊ ψ η d₀ Y Q idx)*
      ((markedPhysicalCoordinateIndexGoodVolume e x d₀ Y U Vr idx hR:ℂ)*
        if d.position (Fin.last n)=z₀ then 1 else 0) := by
  cases Subsingleton.elim decJ (Classical.decEq J)
  have hi : (d.position 0).1=(1,0) := (congrArg Subtype.val hd).trans hz₀
  have ha : ∀ v,MarkedPhysicalMarkingDistinct ((idx).1 v) := fun v =>
    markedPhysicalActivePathIndex_distinct (fun j => markedLogPowerBand (e j) x)
      (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) d order v
  have hl : markedPhysicalCoordinateIndexPath (idx).2.1 (Fin.last n)=(1,0) ↔
      d.position (Fin.last n)=z₀ := by
    rw [markedPhysicalActivePathIndex_path _ _ d order hi]
    constructor
    · intro h
      exact Subtype.ext (h.trans hz₀.symm)
    · intro h
      exact (congrArg Subtype.val h).trans hz₀
  unfold markedPhysicalCoordinateCappedTerm markedPhysicalCoordinatePathApply
  dsimp only [markedRawActualPrimeBand,markedPadSlots] at *
  rw [dite_eq_left ha]
  by_cases hc : markedPhysicalCoordinateIndexCoefficient (fun j => markedLogPowerBand (e j) x)
      (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) V ⌊(Real.log x)^(1/100:ℝ)⌋₊ ψ η d₀ Y Q idx≠0
  · rw [dite_eq_left hc]
    have hp := markedPhysicalActivePathIndex_activePath (fun j => markedLogPowerBand (e j) x)
      (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) V ψ η d₀ Y Q d order hi hR ha hc
    rw [hp]
    unfold markedMemoryPathCappedLineContribution
    by_cases hloop : d.position (Fin.last n)=z₀
    · have hiLoop := hl.mpr hloop
      simp only [ite_eq_left hiLoop,ite_eq_left hloop]
      change (markedPhysicalCoordinateIndexGoodVolume e x d₀ Y U Vr idx hR:ℂ)*
          (((∏ j,∏ p : markedRawPrimeBand (markedLogPowerBand (e j) x),markedMemoryBaseline q n p.1:ℝ):ℂ)*
            (markedMemoryPathCappedChoiceSum hZ d q cap:ℂ)*
            markedPhysicalCoordinateIndexCoefficient (fun j => markedLogPowerBand (e j) x)
              (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) V ⌊(Real.log x)^(1/100:ℝ)⌋₊ ψ η d₀ Y Q idx)=
        ((∏ j,∏ p : markedRawPrimeBand (markedLogPowerBand (e j) x),markedMemoryBaseline q n p.1:ℝ):ℂ)*
          (markedMemoryPathCappedChoiceSum hZ d q cap:ℂ)*
          markedPhysicalCoordinateIndexCoefficient (fun j => markedLogPowerBand (e j) x)
            (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) V ⌊(Real.log x)^(1/100:ℝ)⌋₊ ψ η d₀ Y Q idx*
          ((markedPhysicalCoordinateIndexGoodVolume e x d₀ Y U Vr idx hR:ℂ)*1)
      ring
    · have hiLoop : ¬markedPhysicalCoordinateIndexPath (idx).2.1 (Fin.last n)=(1,0) :=
        fun h => hloop (hl.mp h)
      simp only [ite_eq_right hiLoop,ite_eq_right hloop]
      ring
  · rw [dite_eq_right hc]
    have hz := not_not.mp hc
    rw [hz]
    ring

end
end ArtinMatthews
