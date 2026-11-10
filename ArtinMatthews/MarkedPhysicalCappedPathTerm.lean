module

public import ArtinMatthews.MarkedPhysicalCoordinateLineTerms
public import ArtinMatthews.MarkedPhysicalActivePathIndex
public import ArtinMatthews.MarkedPhysicalActivePathReindex
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init


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
