module

public import ArtinMatthews.MarkedMemoryStageTests
public import ArtinMatthews.MarkedMemoryAlternatingStage
public import ArtinMatthews.MarkedMemoryCappedPathAssembly
public import ArtinMatthews.MarkedMemoryPathOrphanTailData
public import ArtinMatthews.MarkedMemoryTiltRescale
public import ArtinMatthews.MarkedPhysicalCappedHistoryFunctional
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

/-! The exact alternating coordinate/history join with arbitrary original
endpoint cutoffs and complete-history tests. No symmetry or constancy of
these tests is assumed; their actual ordered arguments remain visible. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J]
  (P : J → Finset ℕ) (hP : ∀ j p,p∈P j → p.Prime)
  (hdis : ∀ j k,j≠k → Disjoint (markedRawPrimeBand (P j)) (markedRawPrimeBand (P k)))
  {pads B R n : ℕ}
  (hZ : ∀ z∈markedPrimitiveCoordinateTube R,IsCoprime z.1 z.2)
  (V : J → ℝ) (hV : ∀ j,V j≠0) (q : ℝ)
  (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q : ℝ)
  (s : MarkedRawState (fun j => markedRawPrimeBand (P j)) (pads+1) B (markedPrimitiveCoordinateTube R))
  (hs : s.1.1=(1,0)) (hempty : ∀ j,(s.2.2.1.1 j:ℕ)=0)

include hV hs hempty in
theorem markedPhysicalCappedHistory_test_functional
    (ρ : ℝ) (hρ : ρ≠0)
    (χ : ℕ → MarkedRawState (fun j => markedRawPrimeBand (P j)) (pads+1) B
      (markedPrimitiveCoordinateTube R) → ℂ)
    (F : MarkedMemoryChronologicalHistory hZ n s → ℂ) :
    (markedRawStateMass (markedMemoryTiltAtoms V q n) s:ℂ)*
      (∑ H : MarkedMemoryPrimeSupportedHistory (n := n) hZ s,
        markedMemoryGeometricHistoryWeight (markedMemoryTiltAtoms V q n) V hZ ψ η d₀ Y Q ρ
          markedMemoryAlternatingOrientation (markedMemoryHistoryVisitSchedule q n) χ n 0 H.1 * F H.1)=
      (markedPhysicalMass V (pads+1):ℂ)*
        ∑ i : MarkedMemoryCappedPathDecoratedIndex (n := n) hZ s,
          ((markedMemoryPathPrimeChoiceWeight hZ i.1.path q i.1.choices /
            markedMemoryIndependentBirthFactorials hZ
              (markedMemoryCappedPathIndependent (B := B) hZ i.1.path i.1.choices
                i.1.compatible i.1.capacity i.2.1):ℝ):ℂ)*
          markedPhysicalCoordinateIndexCoefficient P hP V pads ψ η d₀ Y Q
            (markedPhysicalMemoryHistoryIndex P hP hZ (markedMemoryCappedPathDecoratedAssembly hZ hdis s i))*
          (markedMemoryStageTestProduct hZ
            (fun k => if markedMemoryAlternatingOrientation k then fun u => star (χ k u) else χ k)
            n 0 (markedMemoryCappedPathDecoratedAssembly hZ hdis s i)*
            F (markedMemoryCappedPathDecoratedAssembly hZ hdis s i)) := by
  have hh := markedPhysicalCappedHistory_functional P hP hdis hZ V hV q ψ η d₀ Y Q s hs hempty ρ hρ
    (fun H => markedMemoryStageTestProduct hZ
      (fun k => if markedMemoryAlternatingOrientation k then fun u => star (χ k u) else χ k) n 0 H*F H)
  apply Eq.trans ?_ hh
  congr 1
  apply Finset.sum_congr rfl
  intro H _
  rw [markedMemoryGeometricHistoryWeight_test_factor]
  ring

end
end ArtinMatthews
