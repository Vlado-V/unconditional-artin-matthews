module

public import ArtinMatthews.MarkedMemoryEndpointFactors
public import ArtinMatthews.MarkedMemoryIndependentEdgeOrder


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
