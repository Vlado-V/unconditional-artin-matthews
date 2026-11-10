module

public import ArtinMatthews.MarkedPhysicalMemoryHistoryCoefficient
public import ArtinMatthews.MarkedMemoryHistoryPhaseFactor
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
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import Std.Tactic.BVDecide.Normalize.BitVec


set_option backward.privateInPublic true
@[expose] public section

/-! The physical even/odd kernels are the literal oriented history
weight already used by the signed birth-distinct boundary pairing. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

def markedMemoryAlternatingOrientation (k : ℕ) : Bool := decide (k%2≠0)

variable {J : Type*} [Fintype J] [DecidableEq J]
  {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
  (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
  (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ)
  (qStage : ℕ → ℝ)

theorem markedMemoryGeometricHistoryWeight_alternating
    (n offset : ℕ) {s : MarkedRawState P (pads+1) B Z}
    (H : MarkedMemoryChronologicalHistory hZ n s) :
    markedMemoryGeometricHistoryWeight ν V hZ ψ η d₀ Y Q ρ markedMemoryAlternatingOrientation
      qStage (fun _ _ => 1) n offset H=
      markedMemoryStageWeight hZ (markedMemoryAlternatingPsi ψ) (markedMemoryAlternatingEta η)
        d₀ Y Q (fun _ _ => 1) ν V ρ qStage n offset H := by
  rw [markedMemoryGeometricHistoryWeight_stage]
  have hp : (fun k => if markedMemoryAlternatingOrientation k then markedRawEdgeAdjointCutoff ψ else ψ)=
      markedMemoryAlternatingPsi ψ := by
    funext k
    by_cases hk : k%2=0 <;> simp [markedMemoryAlternatingOrientation,markedMemoryAlternatingPsi,hk]
  have he : (fun k => if markedMemoryAlternatingOrientation k then fun u => star (η u) else η)=
      markedMemoryAlternatingEta η := by
    funext k
    by_cases hk : k%2=0 <;> simp [markedMemoryAlternatingOrientation,markedMemoryAlternatingEta,hk]
  rw [hp,he]
  congr 1
  funext k u
  simp only [star_one,ite_self]

end
end ArtinMatthews
