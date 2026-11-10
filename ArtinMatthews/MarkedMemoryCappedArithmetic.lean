module

public import ArtinMatthews.MarkedMemoryCappedPathAssembly
public import ArtinMatthews.MarkedMemoryHistoryArithmetic
public import ArtinMatthews.MarkedMemoryPathOrphanTailData
public import ArtinMatthews.MarkedMemoryTiltRescale
public import ArtinMatthews.MarkedMemoryCappedPathEquiv
public import ArtinMatthews.MarkedMemoryCappedPathIndependent
public import ArtinMatthews.MarkedMemoryCappedTiltCoefficient
public import ArtinMatthews.MarkedMemoryIndependentArithmetic
public import ArtinMatthews.MarkedMemoryStageWeights
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

/-! Kernel-independent source normalization on the actual capped path
carrier. The scalar identity can be multiplied by an arbitrary complete
history functional, so it does not identify distinct edge kernels. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] [hJ : DecidableEq J] {P : J → Finset Nat.Primes}
  {pads B n : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
  (hP : ∀ i j,i≠j → Disjoint (P i) (P j))
  (s : MarkedRawState P (pads+1) B Z)
  (V : J → ℝ) (hV : ∀ j,V j≠0) (q : ℝ)

include hV in
theorem markedMemoryCappedPath_tilt_arithmetic
    (i : MarkedMemoryCappedPathDecoratedIndex (n := n) hZ s) :
    markedRawStateMass (markedMemoryTiltAtoms (P := P) V q n) s *
      markedMemoryHistoryArithmeticWeight (markedMemoryTiltAtoms (P := P) V q n) V hZ
        (markedMemoryHistoryVisitSchedule q n) 0 (markedMemoryCappedPathDecoratedAssembly hZ hP s i)=
      markedPhysicalMass V (pads+1) * (∏ j,(V j)⁻¹)^n *
        (markedMemoryPathPrimeChoiceWeight hZ i.1.path q i.1.choices /
          markedMemoryIndependentBirthFactorials hZ
            (markedMemoryCappedPathIndependent (B := B) hZ i.1.path i.1.choices
              i.1.compatible i.1.capacity i.2.1)) := by
  have hdec : hJ=Classical.decEq J := Subsingleton.elim _ _
  cases hdec
  let raw := markedMemoryCappedPathIndependent (B := B) hZ i.1.path i.1.choices
    i.1.compatible i.1.capacity i.2.1
  let hs := (markedMemoryCappedPathIndependent_source hZ hP i.1.path i.1.choices
    i.1.compatible i.1.capacity i.2.1).trans i.1.source
  have hw := markedMemoryIndependent_tilt_source_arithmetic hZ raw i.2.2
    (markedMemoryCappedPathIndependent_prime_injective (B := B) hZ i.1.path i.1.choices
      i.1.compatible i.1.capacity i.2.1 hP)
    (markedMemoryCappedPathIndependent_initial (B := B) hZ i.1.path i.1.choices
      i.1.compatible i.1.capacity i.2.1)
    (markedMemoryCappedPathIndependent_terminal (B := B) hZ i.1.path i.1.choices
      i.1.compatible i.1.capacity i.2.1)
    (markedMemoryCappedPathIndependent_normalized (B := B) hZ i.1.path i.1.choices
      i.1.compatible i.1.capacity i.2.1)
    (markedMemoryCappedPathIndependent_anchor (B := B) hZ i.1.path i.1.choices
      i.1.compatible i.1.capacity i.2.1 hP i.2.2) V hV q
  rw [markedMemoryCappedPath_choiceProduct hZ hP s i q] at hw
  have hm := congrArg (markedRawStateMass (markedMemoryTiltAtoms (P := P) V q n)) hs
  have ht := markedMemoryHistoryArithmeticWeight_transport hZ
    (markedMemoryTiltAtoms (P := P) V q n) V (markedMemoryHistoryVisitSchedule q n) 0 hs
    (markedMemoryIndependentHistory hZ raw i.2.2)
  exact (congrArg₂ (fun a b : ℝ => a*b) hm.symm ht).trans hw

include hV in
theorem markedMemoryCappedPath_tilt_functional
    (hempty : ∀ j,(s.2.2.1.1 j:ℕ)=0)
    (F : MarkedMemoryChronologicalHistory hZ n s → ℂ) :
    (markedRawStateMass (markedMemoryTiltAtoms (P := P) V q n) s:ℂ) *
      (∑ H : MarkedMemoryPrimeSupportedHistory (n := n) hZ s,
        (markedMemoryHistoryArithmeticWeight (markedMemoryTiltAtoms (P := P) V q n) V hZ
          (markedMemoryHistoryVisitSchedule q n) 0 H.1:ℂ)*F H.1)=
      (markedPhysicalMass V (pads+1):ℂ)*(((∏ j,(V j)⁻¹:ℝ):ℂ)^n)*
        ∑ i : MarkedMemoryCappedPathDecoratedIndex (n := n) hZ s,
          ((markedMemoryPathPrimeChoiceWeight hZ i.1.path q i.1.choices /
            markedMemoryIndependentBirthFactorials hZ
              (markedMemoryCappedPathIndependent (B := B) hZ i.1.path i.1.choices
                i.1.compatible i.1.capacity i.2.1):ℝ):ℂ)*
            F (markedMemoryCappedPathDecoratedAssembly hZ hP s i) := by
  have hs := markedMemoryCappedPath_supported_sum hZ hP s hempty
    (fun H => (markedMemoryHistoryArithmeticWeight (markedMemoryTiltAtoms (P := P) V q n) V hZ
      (markedMemoryHistoryVisitSchedule q n) 0 H:ℂ)*F H)
  apply (congrArg (fun z : ℂ => (markedRawStateMass (markedMemoryTiltAtoms (P := P) V q n) s:ℂ)*z) hs).trans
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hh := congrArg (fun r : ℝ => (r:ℂ))
    (markedMemoryCappedPath_tilt_arithmetic hZ hP s V hV q i)
  push_cast at hh
  rw [← mul_assoc,hh]
  push_cast
  ring

end
end ArtinMatthews
