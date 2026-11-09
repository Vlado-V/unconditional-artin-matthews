module

public import ArtinMatthews.MarkedMemoryIndependentIntervalRecover
public import ArtinMatthews.MarkedMemoryIndependentActiveAnchor


set_option backward.privateInPublic true
@[expose] public section

/-! The actual normalized, anchor-admissible independent tableau with
empty endpoint queues yields a compatible one-lifespan choice for each
identity. Active coherence is derived from literal nonzero edge support
through the checked history anchor interface. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] {A : J → Type*}
  [∀ j,Fintype (A j)] [∀ j,DecidableEq (A j)]
  {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)

def markedMemoryIndependentPositionLines (j : J) (a : A j) :
    Fin (n+1) → MarkedRawPrimeLine (d.particle j a).1.1 :=
  fun v => markedPrimePositionLine ((d.particle j a).1.1:ℕ)
    (d.position v.val).1 (hZ _ (d.position v.val).2)

def markedMemoryIndependentBirthVertex (j : J) (a : A j) : Fin (n+1) :=
  ⟨(d.lifespan j).first a/2,by
    have hf := (d.lifespan j).nonempty a
    have hl := (d.lifespan j).bounded a
    omega⟩

omit [∀ j,DecidableEq (A j)] in
theorem markedMemoryIndependent_birth_line (hn : MarkedMemoryBirthNormalized hZ d) (j : J) (a : A j) :
    (d.particle j a).2=markedMemoryIndependentPositionLines hZ d j a
      (markedMemoryIndependentBirthVertex hZ d j a) := by
  have hp := hn j a
  exact eq_of_heq (Sigma.mk.inj hp).2

variable (order : Fin n → J → Equiv.Perm (Fin pads))

local notation "H" => markedMemoryIndependentHistory hZ d order
local notation "V" j:max a:max => markedMemoryIndependentIdentityVisits hZ d j a
local notation "C" j:max a:max => markedMemoryIndependentIntervalChoice hZ d j a
local notation "line" j:max a:max => markedMemoryIndependentPositionLines hZ d j a

theorem markedMemoryIndependent_active_line
    (hempty : ∀ j,(d.lifespan j).initial=[])
    (hn : MarkedMemoryBirthNormalized hZ d)
    (ha : MarkedMemoryHistoryAnchorAdmissible hZ H)
    (j : J) (a : A j) (v : Fin (n+1)) (hv : v∈V j a) :
    (d.particle j a).2= (line j a) v := by
  have hp := markedMemoryIndependent_identity_active_anchor hZ d order hempty hn ha j a v hv
  exact eq_of_heq (Sigma.mk.inj hp).2

omit [∀ j,DecidableEq (A j)] in
theorem markedMemoryIndependent_death_line (j : J) (a : A j) (v : Fin (n+1))
    (hl : (d.lifespan j).last a=2*v.val) : (d.particle j a).2= (line j a) v := by
  apply d.ghost_death_hit v.val (by omega) j a
  · exact (d.lifespan j).nonempty a |>.trans hl.le
  · exact hl
  · intro hv
    have hm := (markedMemoryIndependentIdentityVisits_mem hZ d j a v).mpr hv
    have hh := (markedMemoryIndependentIdentityVisits_alive hZ d j a v hm).2
    omega

theorem markedMemoryIndependent_interval_compatible_of_active_line
    (hempty : ∀ j,(d.lifespan j).initial=[])
    (hterminal : ∀ j,markedMemoryIndependentQueue hZ d (2*n+1) j=[])
    (hn : MarkedMemoryBirthNormalized hZ d)
    (hactive : ∀ j a v,v∈V j a → (d.particle j a).2=(line j a) v)
    (j : J) (a : A j) :
    MarkedMemoryPrimeLifespanCompatible (line j a) (V j a) (C j a) := by
  by_cases hV : (V j a).Nonempty
  · rw [MarkedMemoryPrimeLifespanCompatible,dite_eq_left hV]
    have hmin : (V j a).min' hV∈V j a := Finset.min'_mem _ _
    have hmax : (V j a).max' hV∈V j a := Finset.max'_mem _ _
    have hline := hactive j a
    refine ⟨?_,?_,?_⟩
    · intro v hv
      exact (hline v hv).symm.trans (hline _ hmin)
    · intro v hv
      have hf := markedMemoryIndependentIntervalChoice_first hZ d hempty j a
      simp only [markedMemoryPrimeFirst,hv] at hf
      have hm := (markedMemoryIndependentIdentityVisits_alive hZ d j a _ hmin).1
      have hlt : v<(V j a).min' hV := by change v.val<((V j a).min' hV).val; omega
      have hb : markedMemoryIndependentBirthVertex hZ d j a=v := Fin.ext (by
        change (d.lifespan j).first a/2=v.val
        omega)
      exact ⟨hlt,(congrArg (line j a) hb).symm.trans
        ((markedMemoryIndependent_birth_line hZ d hn j a).symm.trans (hline _ hmin))⟩
    · intro v hv
      have hl := markedMemoryIndependentIntervalChoice_last hZ d hterminal j a
      simp only [markedMemoryPrimeLast,hv] at hl
      have hm := (markedMemoryIndependentIdentityVisits_alive hZ d j a _ hmax).2
      have hlt : (V j a).max' hV<v := by change ((V j a).max' hV).val<v.val; omega
      exact ⟨hlt,(markedMemoryIndependent_death_line hZ d j a v hl.symm).symm.trans (hline _ hmin)⟩
  · rw [MarkedMemoryPrimeLifespanCompatible,dite_eq_right hV]
    have hf : (d.lifespan j).first a%2=1 := by
      by_contra hh
      have hz : (d.lifespan j).first a%2=0 := by omega
      obtain ⟨v,hv,_⟩ := markedMemoryIndependentIdentityVisits_first_even hZ d hempty j a hz
      exact hV ⟨v,hv⟩
    have hl : (d.lifespan j).last a%2=0 := by
      by_contra hh
      have hz : (d.lifespan j).last a%2=1 := by omega
      obtain ⟨v,hv,_⟩ := markedMemoryIndependentIdentityVisits_last_odd hZ d hterminal j a hz
      exact hV ⟨v,hv⟩
    let b := markedMemoryIndependentBirthVertex hZ d j a
    let e : Fin (n+1) := ⟨(d.lifespan j).last a/2,by have hh := (d.lifespan j).bounded a; omega⟩
    have he : (d.lifespan j).last a=2*e.val := by dsimp [e]; omega
    have hfirst : (d.lifespan j).first a=2*b.val+1 := by dsimp [b,markedMemoryIndependentBirthVertex]; omega
    have hbe : b<e := by
      have hh := (d.lifespan j).nonempty a
      change b.val<e.val
      omega
    refine Or.inr ⟨b,e,?_,hbe,?_⟩
    · simp only [markedMemoryIndependentIntervalChoice,markedMemoryPrimeChoiceOfInterval,hf,hl,ite_true]
      rfl
    · exact (markedMemoryIndependent_birth_line hZ d hn j a).symm.trans
        (markedMemoryIndependent_death_line hZ d j a e he)

include order in
theorem markedMemoryIndependent_interval_compatible
    (hempty : ∀ j,(d.lifespan j).initial=[])
    (hterminal : ∀ j,markedMemoryIndependentQueue hZ d (2*n+1) j=[])
    (hn : MarkedMemoryBirthNormalized hZ d)
    (ha : MarkedMemoryHistoryAnchorAdmissible hZ H) (j : J) (a : A j) :
    MarkedMemoryPrimeLifespanCompatible (line j a) (V j a) (C j a) :=
  markedMemoryIndependent_interval_compatible_of_active_line hZ d hempty hterminal hn
    (markedMemoryIndependent_active_line hZ d order hempty hn ha) j a

end
end ArtinMatthews
