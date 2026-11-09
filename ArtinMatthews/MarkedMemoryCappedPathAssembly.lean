module

public import ArtinMatthews.MarkedMemoryCappedPathRecovery
public import ArtinMatthews.MarkedMemoryCappedPathIndex
public import ArtinMatthews.MarkedMemoryIndependentPathSource
public import ArtinMatthews.MarkedMemoryIndependentEndpointGuards


set_option backward.privateInPublic true
@[expose] public section

/-! Literal assembly of the finite capped path/decorations carrier into
original chronological histories. Birth distinctness, all copied-product
gates and empty terminal pending memory are proved, not stored as a
coverage or reconstruction condition in the source index. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads n B : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
  (hP : ∀ i j,i≠j → Disjoint (P i) (P j))

include hP in
theorem markedMemoryCappedPathIndependent_source
    (d : MarkedMemoryActivePathData P pads Z n)
    (c : MarkedMemoryPathPrimeChoices (P := P) (n := n))
    (hc : MarkedMemoryPathChoicesCompatible d hZ c) (hcap : MarkedMemoryPathCapacity hZ d c hc B)
    (births : MarkedMemoryEndpointBirthOrders (markedMemoryPathEndpointData hZ d c hc)) :
    markedMemoryIndependentState hZ
      (markedMemoryCappedPathIndependent (B := B) hZ d c hc hcap births) 0 (Nat.zero_le n)=
        markedMemoryActivePathSource (B := B) d := by
  let raw := markedMemoryCappedPathIndependent (B := B) hZ d c hc hcap births
  let hinj := markedMemoryCappedPathIndependent_prime_injective (B := B) hZ d c hc hcap births hP
  have hs := markedMemoryIndependentActivePath_source hZ raw hinj
    (markedMemoryCappedPathIndependent_initial (B := B) hZ d c hc hcap births)
  have hp := markedMemoryCappedPathIndependent_path (B := B) hZ d c hc hcap births hP
  exact hs.symm.trans (congrArg (markedMemoryActivePathSource (B := B)) hp)

theorem markedMemoryCappedPathIndependent_target_empty
    (d : MarkedMemoryActivePathData P pads Z n)
    (c : MarkedMemoryPathPrimeChoices (P := P) (n := n))
    (hc : MarkedMemoryPathChoicesCompatible d hZ c) (hcap : MarkedMemoryPathCapacity hZ d c hc B)
    (births : MarkedMemoryEndpointBirthOrders (markedMemoryPathEndpointData hZ d c hc))
    (order : Fin n → J → Equiv.Perm (Fin pads)) (j : J) :
    ((markedMemoryChronologicalTarget hZ (markedMemoryIndependentHistory hZ
      (markedMemoryCappedPathIndependent (B := B) hZ d c hc hcap births) order)).2.2.1.1 j:ℕ)=0 := by
  let raw := markedMemoryCappedPathIndependent (B := B) hZ d c hc hcap births
  have he := congrArg (fun u : MarkedRawState P (pads+1) B Z => (u.2.2.1.1 j:ℕ))
    (markedMemoryIndependentHistory_target hZ raw order)
  have hl := congrArg List.length
    (markedMemoryCappedPathIndependent_terminal (B := B) hZ d c hc hcap births j)
  exact he.trans hl

variable (s : MarkedRawState P (pads+1) B Z)

def markedMemoryCappedPathDecoratedAssembly
    (e : MarkedMemoryCappedPathDecoratedIndex (n := n) hZ s) :
    MarkedMemoryChronologicalHistory hZ n s :=
  markedMemoryHistoryTransport hZ
    ((markedMemoryCappedPathIndependent_source hZ hP e.1.path e.1.choices e.1.compatible
      e.1.capacity e.2.1).trans e.1.source)
    (markedMemoryIndependentHistory hZ
      (markedMemoryCappedPathIndependent (B := B) hZ e.1.path e.1.choices e.1.compatible e.1.capacity e.2.1) e.2.2)

theorem markedMemoryCappedPathDecoratedAssembly_anchor
    (e : MarkedMemoryCappedPathDecoratedIndex (n := n) hZ s) :
    MarkedMemoryHistoryAnchorAdmissible hZ (markedMemoryCappedPathDecoratedAssembly hZ hP s e) :=
  (markedMemoryHistoryAnchor_transport hZ _ _).mpr
    (markedMemoryCappedPathIndependent_anchor (B := B) hZ e.1.path e.1.choices e.1.compatible
      e.1.capacity e.2.1 hP e.2.2)

theorem markedMemoryCappedPathDecoratedAssembly_birthDistinct
    (e : MarkedMemoryCappedPathDecoratedIndex (n := n) hZ s) :
    MarkedMemoryHistoryBirthDistinct hZ (markedMemoryCappedPathDecoratedAssembly hZ hP s e) :=
  (markedMemoryHistoryBirthDistinct_transport hZ _ _).mpr
    (markedMemoryCappedPathIndependent_birthDistinct (B := B) hZ e.1.path e.1.choices e.1.compatible
      e.1.capacity e.2.1 hP e.2.2)

theorem markedMemoryCappedPathDecoratedAssembly_target_empty
    (e : MarkedMemoryCappedPathDecoratedIndex (n := n) hZ s) (j : J) :
    ((markedMemoryChronologicalTarget hZ (markedMemoryCappedPathDecoratedAssembly hZ hP s e)).2.2.1.1 j:ℕ)=0 := by
  have he := markedMemoryHistoryTransport_target hZ
    ((markedMemoryCappedPathIndependent_source hZ hP e.1.path e.1.choices e.1.compatible e.1.capacity e.2.1).trans e.1.source)
    (markedMemoryIndependentHistory hZ
      (markedMemoryCappedPathIndependent (B := B) hZ e.1.path e.1.choices e.1.compatible e.1.capacity e.2.1) e.2.2)
  exact (congrArg (fun u : MarkedRawState P (pads+1) B Z => (u.2.2.1.1 j:ℕ)) he).trans
    (markedMemoryCappedPathIndependent_target_empty hZ e.1.path e.1.choices e.1.compatible e.1.capacity e.2.1 e.2.2 j)

def MarkedMemoryPrimeSupportedHistory :=
  {H : MarkedMemoryChronologicalHistory hZ n s // MarkedMemoryHistoryAnchorAdmissible hZ H ∧
    MarkedMemoryHistoryBirthDistinct hZ H ∧ ∀ j,((markedMemoryChronologicalTarget hZ H).2.2.1.1 j:ℕ)=0}

instance markedMemoryPrimeSupportedHistory_fintype : Fintype (MarkedMemoryPrimeSupportedHistory (n := n) hZ s) := by
  unfold MarkedMemoryPrimeSupportedHistory
  infer_instance

def markedMemoryCappedPathSupportedAssembly
    (e : MarkedMemoryCappedPathDecoratedIndex (n := n) hZ s) : MarkedMemoryPrimeSupportedHistory (n := n) hZ s :=
  ⟨markedMemoryCappedPathDecoratedAssembly hZ hP s e,
    markedMemoryCappedPathDecoratedAssembly_anchor hZ hP s e,
    markedMemoryCappedPathDecoratedAssembly_birthDistinct hZ hP s e,
    markedMemoryCappedPathDecoratedAssembly_target_empty hZ hP s e⟩

end
end ArtinMatthews
