module

public import ArtinMatthews.GiantTwoSidedExpandedFourier


set_option backward.privateInPublic true
@[expose] public section

/-! Relabel the original finite groups without changing ordered slots,
pattern choices, or auxiliary labels. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

variable {A J : Type*} (e : A ≃ J) (P : J → Finset ℕ) {k ell : ℕ}

def giantTwoSidedPullMarking (M : ℕ) :
    MarkedPhysicalMarking P M ≃ MarkedPhysicalMarking (P ∘ e) M :=
  (Equiv.piCongrLeft (fun j => Fin M → ↥(P j)) e).symm

@[simp] theorem giantTwoSidedPullMarking_apply {M : ℕ} (a : MarkedPhysicalMarking P M) (j : A) :
    giantTwoSidedPullMarking e P M a j = a (e j) :=
  Equiv.piCongrLeft_symm_apply _ e a j

@[simp] theorem giantTwoSidedPullMarking_symm_apply_apply {M : ℕ}
    (a : MarkedPhysicalMarking (P ∘ e) M) (j : A) :
    (giantTwoSidedPullMarking e P M).symm a (e j) = a j :=
  Equiv.piCongrLeft_apply_apply (fun g => Fin M → ↥(P g)) e a j

def giantTwoSidedPullAuxiliary (C : J → Finset (Fin k)) :
    GiantTwoSidedPatternAuxiliary P C ≃ GiantTwoSidedPatternAuxiliary (P ∘ e) (C ∘ e) :=
  (Equiv.piCongrLeft (fun j => ↥(C j) → ↥(P j)) e).symm

@[simp] theorem giantTwoSidedPullAuxiliary_apply (C : J → Finset (Fin k))
    (z : GiantTwoSidedPatternAuxiliary P C) (j : A) :
    giantTwoSidedPullAuxiliary e P C z j = z (e j) :=
  Equiv.piCongrLeft_symm_apply _ e z j

@[simp] theorem giantTwoSidedPullAuxiliary_symm_apply_apply (C : J → Finset (Fin k))
    (z : GiantTwoSidedPatternAuxiliary (P ∘ e) (C ∘ e)) (j : A) :
    (giantTwoSidedPullAuxiliary e P C).symm z (e j) = z j :=
  Equiv.piCongrLeft_apply_apply (fun g => ↥(C g) → ↥(P g)) e z j

def giantTwoSidedPullCoefficient {C : J → Finset (Fin k)}
    (K : GiantTwoSidedPatternCoefficient P C ell) :
    GiantTwoSidedPatternCoefficient (P ∘ e) (C ∘ e) ell :=
  fun a b z => K ((giantTwoSidedPullMarking e P (k+ell)).symm a)
    ((giantTwoSidedPullMarking e P (k+ell)).symm b) ((giantTwoSidedPullAuxiliary e P C).symm z)

def giantTwoSidedPullSlots (M : ℕ) :
    (J → Equiv.Perm (Fin M)) ≃ (A → Equiv.Perm (Fin M)) :=
  (Equiv.piCongrLeft (fun _ => Equiv.Perm (Fin M)) e).symm

@[simp] theorem giantTwoSidedPullSlots_apply {M : ℕ} (π : J → Equiv.Perm (Fin M)) (j : A) :
    giantTwoSidedPullSlots e M π j = π (e j) :=
  Equiv.piCongrLeft_symm_apply _ e π j

def giantTwoSidedPullEdgeChoice {I : Type*} (patterns : Finset I) (C : I → J → Finset (Fin k)) :
    GiantTwoSidedResidueEdgeChoice (P := P) patterns C ell ≃
      GiantTwoSidedResidueEdgeChoice (P := P ∘ e) patterns (fun p => C p ∘ e) ell :=
  Equiv.sigmaCongrRight (fun p => Equiv.prodCongr (giantTwoSidedPullSlots e (k+ell))
    (Equiv.prodCongr (giantTwoSidedPullSlots e (k+ell)) (giantTwoSidedPullAuxiliary e P (C p.val))))

variable [Fintype A] [Fintype J]

theorem giantTwoSidedPull_bandPrimes :
    markedPhysicalBandPrimes (P ∘ e) = markedPhysicalBandPrimes P := by
  ext p
  simp only [markedPhysicalBandPrimes, Finset.mem_biUnion, Finset.mem_univ, true_and, Function.comp_apply]
  exact ⟨fun ⟨j,hj⟩ => ⟨e j,hj⟩, fun ⟨j,hj⟩ => by
    obtain ⟨a,rfl⟩ := e.surjective j
    exact ⟨a,hj⟩⟩

theorem giantTwoSidedPull_activePrimes {M : ℕ} (a : MarkedPhysicalMarking P M) :
    markedPhysicalActivePrimes (giantTwoSidedPullMarking e P M a) = markedPhysicalActivePrimes a := by
  ext p
  simp only [markedPhysicalActivePrimes, Finset.mem_biUnion, Finset.mem_univ, true_and,
    markedPhysicalLabelSet, Finset.mem_image, giantTwoSidedPullMarking_apply]
  exact ⟨fun ⟨j,hj⟩ => ⟨e j,hj⟩, fun ⟨j,hj⟩ => by
    obtain ⟨b,rfl⟩ := e.surjective j
    exact ⟨b,hj⟩⟩

include e in
theorem giantTwoSidedPull_slotNormalization [DecidableEq A] [DecidableEq J] (M : ℕ) :
    giantTwoSidedResidueSlotNormalization (J := A) M = giantTwoSidedResidueSlotNormalization (J := J) M := by
  unfold giantTwoSidedResidueSlotNormalization
  rw [Fintype.card_congr (giantTwoSidedPullSlots e M).symm]

end
end ArtinMatthews
