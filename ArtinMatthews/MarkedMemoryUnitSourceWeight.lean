module

public import ArtinMatthews.MarkedMemoryNormalizedEndpointWeight
public import ArtinMatthews.MarkedMemoryIndependentWeight
public import ArtinMatthews.MarkedMemoryInitialMeasure
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

/-! At V=1 the original source measure supplies the initial atoms, and
the literal history weight has exactly one atom per actual identity.
Birth factorials and the full ordered edge residual remain separate. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] {A : J → Type*}
  [∀ j,Fintype (A j)] [∀ j,DecidableEq (A j)]
  {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)
  (hempty : ∀ j,(d.lifespan j).initial=[]) (order : Fin n → J → Equiv.Perm (Fin pads))
  (atom : (j : J) → ↥(P j) → ℝ) (q : ℝ)
  (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q : ℝ)
  (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ)

local notation "H" => markedMemoryIndependentHistory hZ d order

include hempty in
theorem markedMemoryIndependent_unit_source_weight :
    (markedRawStateMass atom (markedMemoryIndependentState hZ d 0 (Nat.zero_le n)):ℂ)*
      markedMemoryChronologicalWeight atom (fun _ => 1) hZ ψ η d₀ Y Q 1
        (markedMemoryHistoryVisitSchedule q n) χ n 0 H=
      (((∏ a : Σ j,A j,atom a.1 (d.particle a.1 a.2).1*markedMemoryIndependentEndpointScalar hZ d q a)/
        markedMemoryIndependentBirthFactorials hZ d:ℝ):ℂ)*
          markedMemoryHistoryEdgeResidualProduct hZ ψ η d₀ Y Q χ n 0 H := by
  have hp : markedRawStateMass atom (markedMemoryIndependentState hZ d 0 (Nat.zero_le n))*
      (∏ a : Σ j,A j,markedMemoryIndependentBirthMass hZ d atom (fun _ => 1) a*
        markedMemoryIndependentEndpointScalar hZ d q a)=
      ∏ a : Σ j,A j,atom a.1 (d.particle a.1 a.2).1*markedMemoryIndependentEndpointScalar hZ d q a := by
    simpa only [markedMemoryCompletedBirthMass,ite_self,one_mul] using
      markedMemory_source_birth_product hZ d hempty atom (fun _ => 1)
        (markedMemoryIndependentEndpointScalar hZ d q)
  rw [markedMemoryIndependent_source_lifespan_weight]
  simp only [inv_one,one_pow,mul_one,← markedMemoryIndependentEndpointScalar_eq]
  calc
    _ = (((markedRawStateMass atom (markedMemoryIndependentState hZ d 0 (Nat.zero_le n))*
        (∏ a : Σ j,A j,markedMemoryIndependentBirthMass hZ d atom (fun _ => 1) a*
          markedMemoryIndependentEndpointScalar hZ d q a))/markedMemoryIndependentBirthFactorials hZ d:ℝ):ℂ)*
            markedMemoryHistoryEdgeResidualProduct hZ ψ η d₀ Y Q χ n 0 H := by
      push_cast
      ring
    _ = _ := by rw [hp]

end
end ArtinMatthews
