module

public import ArtinMatthews.MarkedPhysicalCappedGoodVolume
public import ArtinMatthews.MarkedMemoryActivePathFinite
public import ArtinMatthews.MarkedMemoryPathCapacityExpansion
public import ArtinMatthews.MarkedPhysicalActivePathIndex
public import ArtinMatthews.MarkedPhysicalCappedDecoratedSum
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

/-! The original decorated good-volume sum as a sum over actual active
paths and their copied ordering. The genuine ordered-birth fibers cancel
exactly their existing factorials, and the physical sigma mass remains
outside the sum. The literal geometric coefficient and good volume are
both retained at the canonical coordinate index. -/

namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

theorem markedPhysicalCappedGoodVolumeSum_path
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x : ℝ) {B R n : ℕ}
    (hZ : ∀ z ∈ markedPrimitiveCoordinateTube R, IsCoprime z.1 z.2)
    (hdis : ∀ j k, j ≠ k →
      Disjoint (markedRawActualPrimeBand e x j) (markedRawActualPrimeBand e x k))
    (V : J → ℝ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q q U Vr : ℝ) (hR : 1 ≤ R) (z₀ : ↥(markedPrimitiveCoordinateTube R)) :
    markedPhysicalCappedGoodVolumeSum (B := B) (n := n)
        e x hZ hdis V ψ η d₀ Y Q q U Vr hR z₀ =
      (markedPhysicalMass V (markedPadSlots x):ℂ)*
        ∑ d : {d : MarkedMemoryActivePathData (markedRawActualPrimeBand e x)
          ⌊(Real.log x)^(1/100:ℝ)⌋₊ (markedPrimitiveCoordinateTube R) n // d.position 0 = z₀},
          (markedMemoryPathCappedChoiceSum hZ d.1 q B:ℂ)*
            ∑ order : Fin n → J → Equiv.Perm (Fin ⌊(Real.log x)^(1/100:ℝ)⌋₊),
              markedPhysicalCoordinateIndexCoefficient (fun j => markedLogPowerBand (e j) x)
                (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1)
                V ⌊(Real.log x)^(1/100:ℝ)⌋₊ ψ η d₀ Y Q
                (markedPhysicalActivePathIndex (fun j => markedLogPowerBand (e j) x)
                  (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) d.1 order)*
              (markedPhysicalCoordinateIndexGoodVolume e x d₀ Y U Vr
                (markedPhysicalActivePathIndex (fun j => markedLogPowerBand (e j) x)
                  (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) d.1 order) hR:ℂ)*
              if d.1.position (Fin.last n) = z₀ then 1 else 0 := by
  let F : MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x)
      (markedPadSlots x) n R → ℂ := fun i =>
    markedPhysicalCoordinateIndexCoefficient (fun j => markedLogPowerBand (e j) x)
      (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1)
      V ⌊(Real.log x)^(1/100:ℝ)⌋₊ ψ η d₀ Y Q i *
        (markedPhysicalCoordinateIndexGoodVolume e x d₀ Y U Vr i hR:ℂ)
  have hs := markedPhysicalCappedDecorated_sum
    (pads := ⌊(Real.log x)^(1/100:ℝ)⌋₊) (B := B) (n := n)
    (fun j => markedLogPowerBand (e j) x)
    (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) hdis hZ z₀ q F
  unfold markedPhysicalCappedGoodVolumeSum
  calc
    _ = (markedPhysicalMass V (markedPadSlots x):ℂ)*
        ∑ a : MarkedRawActive (markedRawActualPrimeBand e x) (⌊(Real.log x)^(1/100:ℝ)⌋₊+1),
          ∑ i : MarkedMemoryCappedPathDecoratedIndex (n := n)
              hZ (markedMemoryBoundarySource (B := B) z₀ a),
            ((markedMemoryPathPrimeChoiceWeight hZ i.1.path q i.1.choices /
              markedMemoryIndependentBirthFactorials hZ
                (markedMemoryCappedPathIndependent (B := B) hZ i.1.path i.1.choices
                  i.1.compatible i.1.capacity i.2.1):ℝ):ℂ)*
              F (markedPhysicalMemoryHistoryIndex (fun j => markedLogPowerBand (e j) x)
                (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) hZ
                (markedMemoryCappedPathDecoratedAssembly hZ hdis
                  (markedMemoryBoundarySource (B := B) z₀ a) i))*
              markedRawBoundary z₀ (markedMemoryChronologicalTarget hZ
                (markedMemoryCappedPathDecoratedAssembly hZ hdis
                  (markedMemoryBoundarySource (B := B) z₀ a) i)) := by
      apply congrArg (fun t : ℂ => (markedPhysicalMass V (markedPadSlots x):ℂ)*t)
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro i _
      dsimp only [F, markedPhysicalMemoryHistoryActualIndex]
      ring
    _ = _ := congrArg (fun t : ℂ => (markedPhysicalMass V (markedPadSlots x):ℂ)*t) hs

end
end ArtinMatthews
