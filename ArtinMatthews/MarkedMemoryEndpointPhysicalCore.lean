module

public import ArtinMatthews.MarkedMemoryEndpointFactors
public import ArtinMatthews.MarkedMemoryHistoryEdgeVertices
public import ArtinMatthews.MarkedMemoryIndependentEdgeOrder
public import ArtinMatthews.MarkedMemoryIndependentEdgeProduct
public import ArtinMatthews.MarkedMemoryPhysicalCoreMemory
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

/-! A concrete physical specialization of the full decoration quotient.
At rho=1, position-only endpoint multipliers and terminal observables
are proved invariant under birth and copied-slot orders. Arbitrary
history guards and order-sensitive tests keep their exact average in
MarkedMemoryEndpointSum. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B n : ℕ} {Z : Finset (ℤ × ℤ)} {A : J → Type*}
  [∀ j,Fintype (A j)] [∀ j,DecidableEq (A j)]
  (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
  (e : MarkedMemoryEndpointFamily (A := A) (n := n) hZ s)
  (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q : ℝ)

theorem markedMemoryEndpointRawEdge_position_births
    (F : Z → ℂ) (left right : MarkedMemoryEndpointBirthOrders e.1)
    (v : ℕ) (hv : v < n) (order : J → Equiv.Perm (Fin pads)) :
    markedMemoryRawEdgeValue hZ ψ η d₀ Y Q (fun u => F u.1)
      (markedMemoryIndependentEdge hZ (markedMemoryEndpointIndependent hZ s e left) v hv order) =
    markedMemoryRawEdgeValue hZ ψ η d₀ Y Q (fun u => F u.1)
      (markedMemoryIndependentEdge hZ (markedMemoryEndpointIndependent hZ s e right) v hv order) := by
  rw [markedMemoryIndependentRawEdge_joint,markedMemoryIndependentRawEdge_joint]
  apply markedRawEdgeJointCoefficient_one_positionTest hZ ψ η d₀ Y Q F
  all_goals rfl

theorem markedMemoryEndpointRawProduct_position_decorations
    (F : ℕ → Z → ℂ) (left right : MarkedMemoryEndpointBirthOrders e.1)
    (lo ro : Fin n → J → Equiv.Perm (Fin pads)) (offset : ℕ) :
    markedMemoryHistoryRawEdgeProduct hZ ψ η d₀ Y Q (fun t u => F t u.1) n offset
      (markedMemoryIndependentHistory hZ (markedMemoryEndpointIndependent hZ s e left) lo) =
    markedMemoryHistoryRawEdgeProduct hZ ψ η d₀ Y Q (fun t u => F t u.1) n offset
      (markedMemoryIndependentHistory hZ (markedMemoryEndpointIndependent hZ s e right) ro) := by
  calc
    _ = markedMemoryHistoryRawEdgeProduct hZ ψ η d₀ Y Q (fun t u => F t u.1) n offset
        (markedMemoryIndependentHistory hZ (markedMemoryEndpointIndependent hZ s e left) ro) :=
      markedMemoryIndependentRawProduct_position_order hZ (markedMemoryEndpointIndependent hZ s e left)
        ψ η d₀ Y Q F lo ro offset
    _ = _ := by
      rw [markedMemoryIndependent_rawEdgeProduct,markedMemoryIndependent_rawEdgeProduct]
      exact Finset.prod_congr rfl (fun v _ =>
        markedMemoryEndpointRawEdge_position_births hZ s e ψ η d₀ Y Q (F (offset+v.val)) left right v.val v.2 _)

theorem markedMemoryEndpointFamily_target_position
    (births : MarkedMemoryEndpointBirthOrders e.1) (order : Fin n → J → Equiv.Perm (Fin pads)) :
    (markedMemoryChronologicalTarget hZ (markedMemoryNormalizedHistoryAssembly hZ s
      (markedMemoryEndpointFamilyIndex hZ s e births order))).1 = (markedMemoryEndpointBase e.1).positionAt n := by
  have ht := markedMemoryHistoryTransport_target hZ (markedMemoryEndpointFamilyTableau_source hZ s e births)
    (markedMemoryIndependentHistory hZ (markedMemoryEndpointIndependent hZ s e births) order)
  have hi := markedMemoryIndependentHistory_target hZ (markedMemoryEndpointIndependent hZ s e births) order
  exact (congrArg (fun u : MarkedRawState P (pads+1) B Z => u.1) ht).trans
    ((congrArg (fun u : MarkedRawState P (pads+1) B Z => u.1) hi).trans rfl)

def markedMemoryEndpointPhysicalKernel (F : ℕ → Z → ℂ) (G : Z → ℂ) : ℂ :=
  markedMemoryHistoryRawEdgeProduct hZ ψ η d₀ Y Q (fun t u => F t u.1) n 0
    (markedMemoryIndependentHistory hZ
      (markedMemoryEndpointIndependent hZ s e (markedMemoryEndpointCanonicalBirths e.1))
      (fun _ _ => Equiv.refl _)) * G ((markedMemoryEndpointBase e.1).positionAt n)


end
end ArtinMatthews
