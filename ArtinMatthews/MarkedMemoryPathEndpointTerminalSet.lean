module

public import ArtinMatthews.MarkedMemoryPathEndpointLaws
public import ArtinMatthews.MarkedMemoryPrimeLifespanTerminal


set_option backward.privateInPublic true
@[expose] public section

/-! The derived bare endpoint family has no pending identity after
its final ghost. This is a literal finite-set statement, valid before
choosing any order for a birth batch. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2) (d : MarkedMemoryActivePathData P pads Z n)
  (c : (j : J) → ↥(P j) → MarkedMemoryPrimeLifespanChoice n)
  (hc : MarkedMemoryPathChoicesCompatible d hZ c)

local notation "C" => markedMemoryEndpointCanonicalData (markedMemoryPathEndpointData hZ d c hc)

theorem markedMemoryPathEndpoint_terminal_pending (j : J) : (C).pendingAt (2*n+1) j=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  have hm := (Finset.mem_filter.mp ha).2
  have hl : markedMemoryPrimeLast (markedMemoryPathVisits d j a.1) (c j a.1)=2*n+1 := by
    have hb := markedMemoryPrimeLast_bound (markedMemoryPathVisits d j a.1) (c j a.1)
    have hle := hm.2.1
    change 2*n+1≤ markedMemoryPrimeLast (markedMemoryPathVisits d j a.1) (c j a.1) at hle
    omega
  have hv := markedMemoryPrimeLast_terminal_active (markedMemoryPathVisits d j a.1) (c j a.1) hl
  have hh := (markedMemoryPathEndpoint_active_odd hZ d c hc (Fin.last n) j a).mpr
    ((markedMemoryPathVisits_mem d j a.1 (Fin.last n)).mp hv)
  exact hm.2.2 hh

end
end ArtinMatthews
