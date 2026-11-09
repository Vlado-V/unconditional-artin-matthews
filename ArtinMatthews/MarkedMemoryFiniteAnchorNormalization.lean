module

public import ArtinMatthews.MarkedMemoryNormalizedAnchors
public import ArtinMatthews.MarkedMemoryFiniteHistory


set_option backward.privateInPublic true
@[expose] public section

/-! Canonical anchor normalization is an explicit idempotent operation
on the finite data. Its fixed-point subtype, restricted to admissible
tableaux, is finite. Actual extracted empty-pending tableaux lie in that
subtype, and restricting them preserves their complete reconstruction. -/
namespace ArtinMatthews
noncomputable section

variable {J : Type*} [Fintype J] {A : J → Type*} [∀ j,Fintype (A j)]
  {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)} {n : ℕ}
  (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)

def markedMemoryFiniteBirthParticle (d : MarkedMemoryFiniteTableauData A P pads Z n)
    (j : J) (a : A j) : MarkedRawParticle (P j) :=
  markedRawAnchoredParticle (P j) (d.particle j a).1
    (d.positionAt (d.firstAt j a/2)).1 (hZ _ (d.positionAt (d.firstAt j a/2)).2)

def markedMemoryFiniteAnchorNormalize (d : MarkedMemoryFiniteTableauData A P pads Z n) :
    MarkedMemoryFiniteTableauData A P pads Z n :=
  { d with particle := markedMemoryFiniteBirthParticle hZ d }

theorem markedMemoryFiniteAnchorNormalize_idempotent
    (d : MarkedMemoryFiniteTableauData A P pads Z n) :
    markedMemoryFiniteAnchorNormalize hZ (markedMemoryFiniteAnchorNormalize hZ d)=
      markedMemoryFiniteAnchorNormalize hZ d := by
  apply MarkedMemoryFiniteTableauData.ext <;> rfl

theorem markedMemoryFiniteAnchorNormalize_fixed_iff
    (d : MarkedMemoryFiniteTableauData A P pads Z n) :
    markedMemoryFiniteAnchorNormalize hZ d=d ↔
      ∀ j a,d.particle j a=markedMemoryFiniteBirthParticle hZ d j a := by
  constructor
  · intro h j a
    exact (congrArg (fun z : MarkedMemoryFiniteTableauData A P pads Z n => z.particle j a) h).symm
  · intro h
    apply MarkedMemoryFiniteTableauData.ext <;> try rfl
    exact funext (fun j => funext (fun a => (h j a).symm))

theorem markedMemoryFiniteAnchorNormalize_particle_prime
    (d : MarkedMemoryFiniteTableauData A P pads Z n) (j : J) (a : A j) :
    ((markedMemoryFiniteAnchorNormalize hZ d).particle j a).1=(d.particle j a).1 := rfl

theorem markedMemoryFiniteAnchorNormalize_admissible_fixed_iff
    (f : MarkedMemoryFiniteTableau (A := A) (P := P) (pads := pads) (B := B) hZ n) :
    markedMemoryFiniteAnchorNormalize hZ f.1=f.1 ↔
      MarkedMemoryBirthNormalized hZ (markedMemoryFiniteTableau_toIndependent hZ f) :=
  markedMemoryFiniteAnchorNormalize_fixed_iff hZ f.1

def MarkedMemoryNormalizedFiniteTableau :=
  {f : MarkedMemoryFiniteTableau (A := A) (P := P) (pads := pads) (B := B) hZ n //
    markedMemoryFiniteAnchorNormalize hZ f.1=f.1}

instance markedMemoryNormalizedFiniteTableau_fintype :
    Fintype (MarkedMemoryNormalizedFiniteTableau (A := A) (P := P) (pads := pads) (B := B) (n := n) hZ) := by
  classical
  unfold MarkedMemoryNormalizedFiniteTableau
  infer_instance

variable [∀ j,DecidableEq (A j)]
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)

def markedMemoryIndependent_toNormalizedFinite (hn : MarkedMemoryBirthNormalized hZ d) :
    MarkedMemoryNormalizedFiniteTableau (A := A) (P := P) (pads := pads) (B := B) (n := n) hZ :=
  ⟨markedMemoryIndependent_toFinite hZ d,
    (markedMemoryFiniteAnchorNormalize_admissible_fixed_iff hZ _).mpr
      (markedMemoryBirthNormalized_restore hZ d hn)⟩

theorem markedMemoryIndependent_toNormalizedFinite_history_heq
    (hn : MarkedMemoryBirthNormalized hZ d) (order : Fin n → J → Equiv.Perm (Fin pads)) :
    HEq (markedMemoryIndependentHistory hZ
        (markedMemoryFiniteTableau_toIndependent hZ (markedMemoryIndependent_toNormalizedFinite hZ d hn).1) order)
      (markedMemoryIndependentHistory hZ d order) :=
  markedMemoryFinite_restore_history_heq hZ d order

def markedMemoryActualNormalizedFinite [DecidableEq J]
    {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s)
    (hempty : ∀ j,(s.2.2.1.1 j:ℕ)=0)
    (ha : MarkedMemoryHistoryAnchorAdmissible hZ history) :
    MarkedMemoryNormalizedFiniteTableau (A := MarkedMemoryActualFiber hZ history)
      (P := P) (pads := pads) (B := B) (n := n) hZ :=
  markedMemoryIndependent_toNormalizedFinite hZ (markedMemoryActualTableau hZ history ha)
    (markedMemoryActualTableau_birthNormalized hZ history hempty ha)

theorem markedMemoryActualNormalizedFinite_val [DecidableEq J]
    {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s)
    (hempty : ∀ j,(s.2.2.1.1 j:ℕ)=0)
    (ha : MarkedMemoryHistoryAnchorAdmissible hZ history) :
    (markedMemoryActualNormalizedFinite hZ history hempty ha).1=
      markedMemoryIndependent_toFinite hZ (markedMemoryActualTableau hZ history ha) := rfl

end
end ArtinMatthews
