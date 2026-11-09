module

public import ArtinMatthews.MarkedMemoryEndpointPhysicalCore
public import ArtinMatthews.MarkedMemoryIndependentPrimeDistinct
public import ArtinMatthews.MarkedMinorArcRawGhostSymmetryBoundary


set_option backward.privateInPublic true
@[expose] public section

/-! Actual performed-birth distinctness and the literal terminal empty
memory boundary descend to bare endpoint data under every birth and
copied-slot decoration. Initial pending memory is empty by construction. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B n : ℕ} {Z : Finset (ℤ × ℤ)} {A : J → Type*}
  [∀ j,Fintype (A j)] [∀ j,DecidableEq (A j)]
  (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
  (e : MarkedMemoryEndpointFamily (A := A) (n := n) hZ s)

def markedMemoryEndpointHistory (births : MarkedMemoryEndpointBirthOrders e.1)
    (order : Fin n → J → Equiv.Perm (Fin pads)) : MarkedMemoryChronologicalHistory hZ n s :=
  markedMemoryNormalizedHistoryAssembly hZ s (markedMemoryEndpointFamilyIndex hZ s e births order)

def MarkedMemoryEndpointPrimeDistinct : Prop :=
  Function.Injective (fun a : Σ j,A j => (e.1.particle a.1 a.2).1.1)

def MarkedMemoryEndpointTerminalEmpty : Prop :=
  ∀ j,((markedMemoryEndpointBase e.1).pendingAt (2*n+1) j).card=0

def markedMemoryEndpointBoundary (z₀ : Z) : ℂ :=
  if (markedMemoryEndpointBase e.1).positionAt n=z₀ ∧ MarkedMemoryEndpointTerminalEmpty hZ s e then 1 else 0

theorem markedMemoryHistoryBirthDistinct_transport
    {u v : MarkedRawState P (pads+1) B Z} (h : u=v) (H : MarkedMemoryChronologicalHistory hZ n u) :
    MarkedMemoryHistoryBirthDistinct hZ (markedMemoryHistoryTransport hZ h H) ↔
      MarkedMemoryHistoryBirthDistinct hZ H := by
  cases h
  rfl

theorem markedMemoryEndpoint_initial_empty (births : MarkedMemoryEndpointBirthOrders e.1) (j : J) :
    ((markedMemoryEndpointIndependent hZ s e births).lifespan j).initial=[] := by
  exact markedMemoryFiniteList_toList_ofList [] List.nodup_nil

theorem markedMemoryEndpoint_birthDistinct_iff (births : MarkedMemoryEndpointBirthOrders e.1)
    (order : Fin n → J → Equiv.Perm (Fin pads)) :
    MarkedMemoryHistoryBirthDistinct hZ (markedMemoryEndpointHistory hZ s e births order) ↔
      MarkedMemoryEndpointPrimeDistinct hZ s e := by
  have ht := markedMemoryHistoryBirthDistinct_transport hZ
    (markedMemoryEndpointFamilyTableau_source hZ s e births)
    (markedMemoryIndependentHistory hZ (markedMemoryEndpointIndependent hZ s e births) order)
  have hi := markedMemoryIndependent_birthDistinct_iff_prime_injective hZ
    (markedMemoryEndpointIndependent hZ s e births) order (markedMemoryEndpoint_initial_empty hZ s e births)
  exact ht.trans (hi.trans Iff.rfl)

theorem markedMemoryEndpoint_memory_size (births : MarkedMemoryEndpointBirthOrders e.1)
    (t : ℕ) (ht : t≤2*n+1) (j : J) :
    ((markedMemoryIndependentMemory hZ (markedMemoryEndpointIndependent hZ s e births) t ht).1.1 j : ℕ) =
      ((markedMemoryEndpointBase e.1).pendingAt t j).card := by
  change (markedMemoryIndependentQueue hZ (markedMemoryEndpointIndependent hZ s e births) t j).length = _
  exact markedMemoryPendingQueueAt_length ((markedMemoryEndpointIndependent hZ s e births).lifespan j) t ht

theorem markedMemoryEndpoint_target_size (births : MarkedMemoryEndpointBirthOrders e.1)
    (order : Fin n → J → Equiv.Perm (Fin pads)) (j : J) :
    (((markedMemoryChronologicalTarget hZ (markedMemoryEndpointHistory hZ s e births order)).2.2.1.1 j) : ℕ) =
      ((markedMemoryEndpointBase e.1).pendingAt (2*n+1) j).card := by
  have ht := markedMemoryHistoryTransport_target hZ (markedMemoryEndpointFamilyTableau_source hZ s e births)
    (markedMemoryIndependentHistory hZ (markedMemoryEndpointIndependent hZ s e births) order)
  have hi := markedMemoryIndependentHistory_target hZ (markedMemoryEndpointIndependent hZ s e births) order
  exact (congrArg (fun u : MarkedRawState P (pads+1) B Z => (u.2.2.1.1 j : ℕ)) ht).trans
    ((congrArg (fun u : MarkedRawState P (pads+1) B Z => (u.2.2.1.1 j : ℕ)) hi).trans
      (markedMemoryEndpoint_memory_size hZ s e births (2*n+1) (Nat.le_refl _) j))

theorem markedMemoryEndpoint_terminal_empty_iff (births : MarkedMemoryEndpointBirthOrders e.1)
    (order : Fin n → J → Equiv.Perm (Fin pads)) :
    (∀ j,((markedMemoryChronologicalTarget hZ (markedMemoryEndpointHistory hZ s e births order)).2.2.1.1 j : ℕ)=0) ↔
      MarkedMemoryEndpointTerminalEmpty hZ s e := by
  simp only [markedMemoryEndpoint_target_size,MarkedMemoryEndpointTerminalEmpty]

omit [∀ j,Fintype (A j)] [∀ j,DecidableEq (A j)] in
theorem markedMemoryRawMemory_empty_iff_sizes (m : MarkedRawMemory P B) :
    m=markedRawBoundaryEmptyMemory P B ↔ ∀ j,(m.1.1 j:ℕ)=0 := by
  constructor
  · intro h j
    exact congrArg (fun u : MarkedRawMemory P B => (u.1.1 j:ℕ)) h
  · intro h
    apply markedRawMemory_eq_empty_of_sizes
    apply Subtype.ext
    funext j
    exact Fin.ext (h j)

theorem markedMemoryEndpoint_boundary_eq (z₀ : Z) (births : MarkedMemoryEndpointBirthOrders e.1)
    (order : Fin n → J → Equiv.Perm (Fin pads)) :
    markedRawBoundary z₀ (markedMemoryChronologicalTarget hZ (markedMemoryEndpointHistory hZ s e births order)) =
      markedMemoryEndpointBoundary hZ s e z₀ := by
  have hp : (markedMemoryChronologicalTarget hZ (markedMemoryEndpointHistory hZ s e births order)).1 =
      (markedMemoryEndpointBase e.1).positionAt n :=
    markedMemoryEndpointFamily_target_position hZ s e births order
  have he := (markedMemoryRawMemory_empty_iff_sizes
    (markedMemoryChronologicalTarget hZ (markedMemoryEndpointHistory hZ s e births order)).2.2).trans
      (markedMemoryEndpoint_terminal_empty_iff hZ s e births order)
  unfold markedRawBoundary markedMemoryEndpointBoundary
  change (if _=z₀ ∧ _ then (1:ℂ) else 0)=_
  simp only [hp,he]

end
end ArtinMatthews
