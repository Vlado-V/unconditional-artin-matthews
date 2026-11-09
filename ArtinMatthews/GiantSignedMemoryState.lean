module

public import ArtinMatthews.GiantTwoSidedResidueState


set_option backward.privateInPublic true
@[expose] public section

/-! The full Source02 pending state has every finite memory degree.
Particles retain their actual prime and residue displacement. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

abbrev GiantSignedParticle (P : Finset ℕ) := Σ p : P, ZMod p.val

abbrev GiantSignedMemory {B : Type*} (P : B → Finset ℕ) :=
  Σ degree : B → ℕ, (g : B) → Fin (degree g) → GiantSignedParticle (P g)

def giantSignedParticleTranslate {P : Finset ℕ} (d : ℤ) :
    GiantSignedParticle P ≃ GiantSignedParticle P where
  toFun p := ⟨p.1, p.2 + (d : ZMod p.1.val)⟩
  invFun p := ⟨p.1, p.2 - (d : ZMod p.1.val)⟩
  left_inv p := by cases p; simp
  right_inv p := by cases p; simp

def giantSignedMemoryTranslate {B : Type*} {P : B → Finset ℕ} (d : ℤ) :
    GiantSignedMemory P ≃ GiantSignedMemory P :=
  Equiv.sigmaCongrRight fun _ => Equiv.piCongrRight fun _ =>
    Equiv.piCongrRight fun _ => giantSignedParticleTranslate d

@[simp] theorem giantSignedMemoryTranslate_degree {B : Type*} {P : B → Finset ℕ}
    (d : ℤ) (m : GiantSignedMemory P) : (giantSignedMemoryTranslate d m).1 = m.1 := rfl

@[simp] theorem giantSignedMemoryTranslate_prime {B : Type*} {P : B → Finset ℕ}
    (d : ℤ) (m : GiantSignedMemory P) (g : B) (i : Fin (m.1 g)) :
    ((giantSignedMemoryTranslate d m).2 g i).1 = (m.2 g i).1 := rfl

@[simp] theorem giantSignedMemoryTranslate_residue {B : Type*} {P : B → Finset ℕ}
    (d : ℤ) (m : GiantSignedMemory P) (g : B) (i : Fin (m.1 g)) :
    ((giantSignedMemoryTranslate d m).2 g i).2 =
      (m.2 g i).2 + (d : ZMod (m.2 g i).1.val) := rfl

def giantSignedMemoryPermute {B : Type*} {P : B → Finset ℕ}
    (m : GiantSignedMemory P) (σ : (g : B) → Equiv.Perm (Fin (m.1 g))) :
    GiantSignedMemory P := ⟨m.1, fun g i => m.2 g (σ g i)⟩

def GiantSignedMemorySymmetric {B : Type*} {P : B → Finset ℕ}
    (f : GiantSignedMemory P → ℂ) : Prop :=
  ∀ m σ, f (giantSignedMemoryPermute m σ) = f m

def giantSignedMemoryMass {B : Type*} [Fintype B] {P : B → Finset ℕ}
    (ν : (g : B) → P g → ℝ) (m : GiantSignedMemory P) : ℝ :=
  ∏ g, (∏ i, ν g (m.2 g i).1) / (Nat.factorial (m.1 g) : ℝ)

theorem giantSignedMemoryMass_nonneg {B : Type*} [Fintype B] {P : B → Finset ℕ}
    (ν : (g : B) → P g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (m : GiantSignedMemory P) :
    0 ≤ giantSignedMemoryMass ν m :=
  Finset.prod_nonneg fun g _ => div_nonneg
    (Finset.prod_nonneg fun i _ => hν g (m.2 g i).1) (Nat.cast_nonneg _)

@[simp] theorem giantSignedMemoryMass_translate {B : Type*} [Fintype B]
    {P : B → Finset ℕ} (ν : (g : B) → P g → ℝ) (d : ℤ) (m : GiantSignedMemory P) :
    giantSignedMemoryMass ν (giantSignedMemoryTranslate d m) = giantSignedMemoryMass ν m := rfl

theorem giantSignedMemoryMass_permute {B : Type*} [Fintype B] {P : B → Finset ℕ}
    (ν : (g : B) → P g → ℝ) (m : GiantSignedMemory P)
    (σ : (g : B) → Equiv.Perm (Fin (m.1 g))) :
    giantSignedMemoryMass ν (giantSignedMemoryPermute m σ) = giantSignedMemoryMass ν m := by
  unfold giantSignedMemoryMass giantSignedMemoryPermute
  apply Finset.prod_congr rfl
  intro g _
  congr 1
  exact Equiv.prod_comp (σ g) (fun i => ν g (m.2 g i).1)

def giantSignedEmptyMemory {B : Type*} (P : B → Finset ℕ) : GiantSignedMemory P :=
  ⟨fun _ => 0, fun _ i => Fin.elim0 i⟩

@[simp] theorem giantSignedEmptyMemory_mass {B : Type*} [Fintype B]
    {P : B → Finset ℕ} (ν : (g : B) → P g → ℝ) :
    giantSignedMemoryMass ν (giantSignedEmptyMemory P) = 1 := by
  simp [giantSignedMemoryMass, giantSignedEmptyMemory]
  exact Finset.prod_eq_one (fun g _ => Fin.prod_univ_zero _)

abbrev GiantSignedState {S B : Type*} [Fintype S]
    (PS : S → Finset ℕ) (PB : B → Finset ℕ) (M : ℕ) :=
  GiantTwoSidedResidueState PS M × (MarkedPhysicalMarking PB M × GiantSignedMemory PB)

def giantSignedActiveMass {B : Type*} [Fintype B] {P : B → Finset ℕ}
    (ν : (g : B) → P g → ℝ) {M : ℕ} (a : MarkedPhysicalMarking P M) : ℝ :=
  ∏ g, ∏ i, ν g (a g i)

def giantSignedStateMass {S B : Type*} [Fintype S] [Fintype B]
    (PS : S → Finset ℕ) {PB : B → Finset ℕ} (ν : (g : B) → PB g → ℝ) {M : ℕ}
    (s : GiantSignedState PS PB M) : ℝ :=
  giantTwoSidedResidueHaarStateMass PS M *
    giantSignedActiveMass ν s.2.1 * giantSignedMemoryMass ν s.2.2

def giantSignedBoundary {S B : Type*} [Fintype S]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {M : ℕ}
    (s : GiantSignedState PS PB M) : ℂ := by
  classical
  exact if s.2.2 = giantSignedEmptyMemory PB then 1 else 0

theorem giantSignedBoundary_empty {S B : Type*} [Fintype S]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {M : ℕ}
    (s : GiantTwoSidedResidueState PS M) (a : MarkedPhysicalMarking PB M) :
    giantSignedBoundary (s, a, giantSignedEmptyMemory PB) = 1 := by
  simp [giantSignedBoundary]

end
end ArtinMatthews
