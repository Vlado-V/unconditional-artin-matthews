module

public import ArtinMatthews.MarkedMemoryAlternatingStage
public import ArtinMatthews.MarkedMemoryBirthEventBoundary
public import ArtinMatthews.MarkedMemoryCappedPathAssembly
public import ArtinMatthews.MarkedMemoryPathOrphanTailData
public import ArtinMatthews.MarkedMemoryStageTests
public import ArtinMatthews.MarkedMemoryTiltRescale
public import ArtinMatthews.MarkedMemoryGeometricSupport
public import ArtinMatthews.MarkedPhysicalCappedHistoryTests
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

/-! The literal birth-distinct oriented boundary pairing has an exact
capped physical-coordinate expansion. Initial nu remains in the source
measure, sigma is factored outside, and the original cap, signs, endpoint
tests and every ordered birth factorial remain unchanged. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J]
  (P : J → Finset ℕ) (hP : ∀ j p,p∈P j → p.Prime)
  (hdis : ∀ j k,j≠k → Disjoint (markedRawPrimeBand (P j)) (markedRawPrimeBand (P k)))
  {pads B R n : ℕ}
  (hZ : ∀ z∈markedPrimitiveCoordinateTube R,IsCoprime z.1 z.2)
  (V : J → ℝ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q : ℝ)
  (z₀ : ↥(markedPrimitiveCoordinateTube R))
  (χ : ℕ → MarkedRawState (fun j => markedRawPrimeBand (P j)) (pads+1) B
    (markedPrimitiveCoordinateTube R) → ℂ)

def markedPhysicalCappedBoundarySum : ℂ :=
  (markedPhysicalMass V (pads+1):ℂ)*
    ∑ a : MarkedRawActive (fun j => markedRawPrimeBand (P j)) (pads+1),
      ∑ i : MarkedMemoryCappedPathDecoratedIndex (n := n) hZ (markedMemoryBoundarySource (B := B) z₀ a),
        ((markedMemoryPathPrimeChoiceWeight hZ i.1.path q i.1.choices /
          markedMemoryIndependentBirthFactorials hZ
            (markedMemoryCappedPathIndependent (B := B) hZ i.1.path i.1.choices
              i.1.compatible i.1.capacity i.2.1):ℝ):ℂ)*
        markedPhysicalCoordinateIndexCoefficient P hP V pads ψ η d₀ Y Q
          (markedPhysicalMemoryHistoryIndex P hP hZ
            (markedMemoryCappedPathDecoratedAssembly hZ hdis (markedMemoryBoundarySource (B := B) z₀ a) i))*
        (markedMemoryStageTestProduct hZ
          (fun k => if markedMemoryAlternatingOrientation k then fun u => star (χ k u) else χ k)
          n 0 (markedMemoryCappedPathDecoratedAssembly hZ hdis (markedMemoryBoundarySource (B := B) z₀ a) i)*
          markedRawBoundary z₀ (markedMemoryChronologicalTarget hZ
            (markedMemoryCappedPathDecoratedAssembly hZ hdis (markedMemoryBoundarySource (B := B) z₀ a) i)))

theorem markedPhysicalBirthDistinctBoundary_eq_capped
    (hV : ∀ j,V j≠0) (hz₀ : z₀.1=(1,0)) (ρ : ℝ) (hρ : ρ≠0) :
    markedMemoryBirthDistinctGeometricBoundaryPairing (N := n)
      (markedMemoryTiltAtoms V q n) V hZ ψ η d₀ Y Q ρ markedMemoryAlternatingOrientation
      (markedMemoryHistoryVisitSchedule q n) χ z₀=
        markedPhysicalCappedBoundarySum (n := n) P hP hdis hZ V ψ η d₀ Y Q q z₀ χ := by
  rw [markedMemoryBirthDistinctGeometricBoundary_supported]
  unfold markedPhysicalCappedBoundarySum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  exact markedPhysicalCappedHistory_test_functional P hP hdis hZ V hV q ψ η d₀ Y Q
    (markedMemoryBoundarySource (B := B) z₀ a) hz₀ (by intro j; rfl) ρ hρ χ
    (fun H => markedRawBoundary z₀ (markedMemoryChronologicalTarget hZ H))

end
end ArtinMatthews
