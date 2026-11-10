module

public import ArtinMatthews.MarkedMemoryHistoryPhaseFactor
public import ArtinMatthews.MarkedMemoryStageWeights
public import ArtinMatthews.MarkedMemoryCopiedSlotGeometry
public import ArtinMatthews.MarkedMemoryGeometricStage
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
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Arbitrary ordered endpoint tests factor without changing their
arguments. The target test is evaluated before the final target slot
permutation, exactly as in the original raw coefficient. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J]
  {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2)

def markedMemoryStageTestProduct (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ) :
    (n offset : ℕ) → {s : MarkedRawState P (pads+1) B Z} →
      MarkedMemoryChronologicalHistory hZ n s → ℂ
  | 0,_,_,_ => 1
  | n+1,k,s,H =>
      χ k (markedRawSlotEquiv H.2.1.1 (markedMemoryGhostChoiceTarget hZ s H.1)) *
      χ k (markedRawEdgeTargetState hZ
        (markedRawSlotEquiv H.2.1.1 (markedMemoryGhostChoiceTarget hZ s H.1)) H.2.1.2.1) *
      markedMemoryStageTestProduct χ n (k+1) H.2.2

theorem markedMemoryEdgeChoiceWeight_test_factor
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (s : MarkedRawState P (pads+1) B Z) (c : MarkedMemoryEdgeChoice hZ s) :
    markedMemoryEdgeChoiceWeight ν V hZ ψ η d₀ Y Q ρ χ s c=
      markedMemoryEdgeChoiceWeight ν V hZ ψ η d₀ Y Q ρ (fun _ => 1) s c *
        χ (markedRawSlotEquiv c.1 s) *
        χ (markedRawEdgeTargetState hZ (markedRawSlotEquiv c.1 s) c.2.1) := by
  unfold markedMemoryEdgeChoiceWeight
  simp_rw [markedRawEdgeChoiceCoefficient_eq_joint]
  rw [markedRawEdgeJointCoefficient_test_factor hZ ψ η d₀ Y Q ρ χ]
  ring

theorem markedMemoryStageWeight_test_factor
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    (ψStage : ℕ → SchwartzMap ℝ ℂ) (ηStage : ℕ → ℝ → ℂ) (d₀ Y Q ρ : ℝ)
    (qStage : ℕ → ℝ) (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ)
    (n offset : ℕ) {s : MarkedRawState P (pads+1) B Z}
    (H : MarkedMemoryChronologicalHistory hZ n s) :
    markedMemoryStageWeight hZ ψStage ηStage d₀ Y Q χ ν V ρ qStage n offset H=
      markedMemoryStageWeight hZ ψStage ηStage d₀ Y Q (fun _ _ => 1) ν V ρ qStage n offset H *
        markedMemoryStageTestProduct hZ χ n offset H := by
  induction n generalizing s offset with
  | zero => simp only [markedMemoryStageWeight,markedMemoryStageTestProduct,mul_one]
  | succ n ih =>
    rw [markedMemoryStageWeight,markedMemoryStageWeight,markedMemoryStageTestProduct,
      markedMemoryEdgeChoiceWeight_test_factor,ih]
    ring

theorem markedMemoryGeometricHistoryWeight_test_factor
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ)
    (orientation : ℕ → Bool) (qStage : ℕ → ℝ)
    (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ)
    (n offset : ℕ) {s : MarkedRawState P (pads+1) B Z}
    (H : MarkedMemoryChronologicalHistory hZ n s) :
    markedMemoryGeometricHistoryWeight ν V hZ ψ η d₀ Y Q ρ orientation qStage χ n offset H=
      markedMemoryGeometricHistoryWeight ν V hZ ψ η d₀ Y Q ρ orientation qStage (fun _ _ => 1) n offset H *
        markedMemoryStageTestProduct hZ (fun k => if orientation k then fun u => star (χ k u) else χ k)
          n offset H := by
  rw [markedMemoryGeometricHistoryWeight_stage,markedMemoryGeometricHistoryWeight_stage]
  have hχ : (fun k => if orientation k then fun _ : MarkedRawState P (pads+1) B Z => star (1:ℂ)
      else fun _ => (1:ℂ))=(fun _ _ => 1) := by
    funext k u
    simp only [star_one,ite_self]
  rw [hχ,markedMemoryStageWeight_test_factor]

end
end ArtinMatthews
