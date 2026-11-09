module

public import ArtinMatthews.MarkedMemoryIndependentActivePath
public import ArtinMatthews.MarkedMemoryIndependentIntervalCompatible


set_option backward.privateInPublic true
@[expose] public section

/-! The inverse primewise choices are computed from genuine identity
intervals. Primes absent from the identity image receive the empty
choice; the local physical path and actual support derive compatibility. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] {A : J → Type*}
  [∀ j,Fintype (A j)] [∀ j,DecidableEq (A j)]
  {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)
  (hinj : Function.Injective (markedMemoryIndependentPrime hZ d))

local notation "path" => markedMemoryIndependentActivePath hZ d hinj
local notation "emb" => markedMemoryIndependentBandPrimeEmbedding hZ d hinj

omit [∀ j,DecidableEq (A j)] in
def markedMemoryIndependentPathChoices : (j : J) → ↥(P j) → MarkedMemoryPrimeLifespanChoice n :=
  fun j p => if hp : ∃ a : A j,(d.particle j a).1=p then
    markedMemoryIndependentIntervalChoice hZ d j (Classical.choose hp) else (none,none)

omit [∀ j,DecidableEq (A j)] in
include hinj in
theorem markedMemoryIndependentPathChoices_at (j : J) (a : A j) :
    markedMemoryIndependentPathChoices hZ d j (d.particle j a).1=
      markedMemoryIndependentIntervalChoice hZ d j a := by
  have hp : ∃ b : A j,(d.particle j b).1=(d.particle j a).1 := ⟨a,rfl⟩
  simp only [markedMemoryIndependentPathChoices,dite_eq_left hp]
  apply congrArg (markedMemoryIndependentIntervalChoice hZ d j)
  apply (emb j).injective
  exact Classical.choose_spec hp

theorem markedMemoryIndependentPathVisits_at (j : J) (a : A j) :
    markedMemoryPathVisits path j (d.particle j a).1=markedMemoryIndependentIdentityVisits hZ d j a := by
  ext v
  rw [markedMemoryPathVisits_mem,markedMemoryIndependentIdentityVisits_mem,d.active_mem v.val (by omega)]
  change (∃ k,emb j (d.activeId v.val j k)=emb j a) ↔ ∃ k,d.activeId v.val j k=a
  constructor
  · rintro ⟨k,hk⟩
    exact ⟨k,(emb j).injective hk⟩
  · rintro ⟨k,hk⟩
    exact ⟨k,congrArg (emb j) hk⟩

theorem markedMemoryIndependentPathVisits_absent (j : J) (p : P j)
    (hp : ¬∃ a : A j,(d.particle j a).1=p) : markedMemoryPathVisits path j p=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  obtain ⟨k,hk⟩ := (markedMemoryPathVisits_mem path j p v).mp hv
  exact hp ⟨d.activeId v.val j k,hk⟩

variable (order : Fin n → J → Equiv.Perm (Fin pads))
local notation "H" => markedMemoryIndependentHistory hZ d order

theorem markedMemoryIndependentPathChoices_compatible
    (hempty : ∀ j,(d.lifespan j).initial=[])
    (hterminal : ∀ j,markedMemoryIndependentQueue hZ d (2*n+1) j=[])
    (hn : MarkedMemoryBirthNormalized hZ d)
    (ha : MarkedMemoryHistoryAnchorAdmissible hZ H) :
    MarkedMemoryPathChoicesCompatible path hZ (markedMemoryIndependentPathChoices hZ d) := by
  intro j p
  by_cases hp : ∃ a : A j,(d.particle j a).1=p
  · obtain ⟨a,rfl⟩ := hp
    rw [markedMemoryIndependentPathVisits_at hZ d hinj j a,
      markedMemoryIndependentPathChoices_at hZ d hinj j a]
    exact markedMemoryIndependent_interval_compatible hZ d order hempty hterminal hn ha j a
  · rw [markedMemoryIndependentPathVisits_absent hZ d hinj j p hp]
    simp only [markedMemoryIndependentPathChoices,dite_eq_right hp,MarkedMemoryPrimeLifespanCompatible,
      Finset.not_nonempty_empty,dite_false]
    exact Or.inl trivial

end
end ArtinMatthews
