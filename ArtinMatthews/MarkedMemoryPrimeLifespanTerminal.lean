module

public import ArtinMatthews.MarkedMemoryPrimeLifespanAnchor


set_option backward.privateInPublic true
@[expose] public section

/-! Boundary and ghost parity of the derived half-step intervals.
In particular, a lifespan reaching the last population is active there,
so the primewise construction ends with empty pending memory. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

variable {N : ℕ} (A : Finset (Fin (N+1))) (c : MarkedMemoryPrimeLifespanChoice N)

theorem markedMemoryPrimeLast_odd_active (v : Fin (N+1))
    (hl : markedMemoryPrimeLast A c=2*v.val+1) : v∈A := by
  cases hb : c.2 with
  | some b => simp only [markedMemoryPrimeLast,hb] at hl; omega
  | none =>
    by_cases hA : A.Nonempty
    · simp only [markedMemoryPrimeLast,hb,dite_eq_left hA] at hl
      have he : A.max' hA=v := Fin.ext (by omega)
      exact he ▸ A.max'_mem hA
    · simp only [markedMemoryPrimeLast,hb,dite_eq_right hA] at hl
      omega

theorem markedMemoryPrimeLast_terminal_active
    (hl : markedMemoryPrimeLast A c=2*N+1) : (Fin.last N)∈A := by
  exact markedMemoryPrimeLast_odd_active A c (Fin.last N) hl

variable {L : Type*} (line : Fin (N+1) → L)

theorem markedMemoryPrimeFirst_ghost_inactive
    (hc : MarkedMemoryPrimeLifespanCompatible line A c) (v : Fin (N+1))
    (hf : markedMemoryPrimeFirst A c=2*v.val+1) : v∉A := by
  intro hv
  have hh := markedMemoryPrimeFirst_active line A c hc v hv
  omega

theorem markedMemoryPrimeLast_ghost_inactive
    (hc : MarkedMemoryPrimeLifespanCompatible line A c) (v : Fin (N+1))
    (hl : markedMemoryPrimeLast A c=2*v.val) : v∉A := by
  intro hv
  have hh := markedMemoryPrimeLast_active line A c hc v hv
  omega

end
end ArtinMatthews
