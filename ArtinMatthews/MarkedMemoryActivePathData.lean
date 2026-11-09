module

public import ArtinMatthews.MarkedMemoryPrimeLifespanAnchor
public import ArtinMatthews.MarkedMinorArcRawState


set_option backward.privateInPublic true
@[expose] public section

/-! A finite active path with its actual single-slot exchanges. The
incoming-not-source condition is the physical ban, retained explicitly;
no claim that an arbitrary sequence of lists has these properties is made. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] (P : J → Finset Nat.Primes)
  (pads : ℕ) (Z : Finset (ℤ × ℤ)) (n : ℕ)

structure MarkedMemoryActivePathData where
  position : Fin (n+1) → Z
  active : Fin (n+1) → (j : J) → Fin (pads+1) ↪ ↥(P j)
  incoming : Fin n → (j : J) → ↥(P j)
  outgoing : Fin n → (j : J) → ↥(P j)
  outgoing_present : ∀ v j,∃ k,active v.castSucc j k=outgoing v j
  incoming_present : ∀ v j,∃ k,active v.succ j k=incoming v j
  incoming_not_source : ∀ v j,¬∃ k,active v.castSucc j k=incoming v j
  exchange : ∀ v j p,(∃ k,active v.succ j k=p) ↔
    ((∃ k,active v.castSucc j k=p) ∧ p≠outgoing v j) ∨ p=incoming v j

variable {P pads Z n}
  (d : MarkedMemoryActivePathData P pads Z n)

def markedMemoryPathVisits (j : J) (p : P j) : Finset (Fin (n+1)) :=
  Finset.univ.filter (fun v => ∃ k,d.active v j k=p)

omit [Fintype J] in
theorem markedMemoryPathVisits_mem (j : J) (p : P j) (v : Fin (n+1)) :
    v∈markedMemoryPathVisits d j p ↔ ∃ k,d.active v j k=p := by
  simp only [markedMemoryPathVisits,Finset.mem_filter,Finset.mem_univ,true_and]

omit [Fintype J] in
theorem markedMemoryPath_incoming_of_new (v : Fin n) (j : J) (p : P j)
    (hn : v.succ∈markedMemoryPathVisits d j p)
    (ho : v.castSucc∉markedMemoryPathVisits d j p) : p=d.incoming v j := by
  rcases (d.exchange v j p).mp ((markedMemoryPathVisits_mem d j p v.succ).mp hn) with h | h
  · exact False.elim (ho ((markedMemoryPathVisits_mem d j p v.castSucc).mpr h.1))
  · exact h

omit [Fintype J] in
theorem markedMemoryPath_outgoing_of_last (v : Fin n) (j : J) (p : P j)
    (ho : v.castSucc∈markedMemoryPathVisits d j p)
    (hn : v.succ∉markedMemoryPathVisits d j p) : p=d.outgoing v j := by
  by_contra hne
  apply hn
  apply (markedMemoryPathVisits_mem d j p v.succ).mpr
  exact (d.exchange v j p).mpr (Or.inl ⟨(markedMemoryPathVisits_mem d j p v.castSucc).mp ho,hne⟩)

omit [Fintype J] in
theorem markedMemoryPath_exchange_distinct (v : Fin n) (j : J) : d.incoming v j≠d.outgoing v j := by
  intro h
  apply d.incoming_not_source v j
  exact (d.outgoing_present v j).imp (fun k hk => hk.trans h.symm)

abbrev MarkedMemoryPathPrimeChoices := (j : J) → ↥(P j) → MarkedMemoryPrimeLifespanChoice n

def MarkedMemoryPathChoicesCompatible
    (hZ : ∀ z∈Z,IsCoprime z.1 z.2) (c : MarkedMemoryPathPrimeChoices (P := P) (n := n)) : Prop :=
  ∀ j p,MarkedMemoryPrimeLifespanCompatible
    (fun v => markedPrimePositionLine (p.1:ℕ) (d.position v).1 (hZ _ (d.position v).2))
    (markedMemoryPathVisits d j p) (c j p)

abbrev MarkedMemoryPathUsedPrime (c : MarkedMemoryPathPrimeChoices (P := P) (n := n)) (j : J) :=
  {p : P j // MarkedMemoryPrimeLifespanUsed (markedMemoryPathVisits d j p) (c j p)}

instance markedMemoryPathUsedPrime_fintype
    (c : MarkedMemoryPathPrimeChoices (P := P) (n := n)) (j : J) :
    Fintype (MarkedMemoryPathUsedPrime d c j) := by infer_instance

end
end ArtinMatthews
