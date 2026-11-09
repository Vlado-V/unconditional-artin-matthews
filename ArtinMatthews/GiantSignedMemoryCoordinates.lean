module

public import ArtinMatthews.GiantSignedMemoryState


set_option backward.privateInPublic true
@[expose] public section

/-! Conditioning the full memory on its degrees and prime lists leaves
the literal finite product of residue rings used for Fourier translation. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

abbrev GiantSignedPrimeLists {B : Type*} (P : B → Finset ℕ) (degree : B → ℕ) :=
  (g : B) → Fin (degree g) → P g

abbrev GiantSignedResidues {B : Type*} {P : B → Finset ℕ} {degree : B → ℕ}
    (primes : GiantSignedPrimeLists P degree) :=
  (g : B) → (i : Fin (degree g)) → ZMod (primes g i).val

def giantSignedMemoryCoordinates {B : Type*} (P : B → Finset ℕ) :
    GiantSignedMemory P ≃ Σ degree : B → ℕ,
      Σ primes : GiantSignedPrimeLists P degree, GiantSignedResidues primes where
  toFun m := ⟨m.1, (fun g i => (m.2 g i).1), fun g i => (m.2 g i).2⟩
  invFun m := ⟨m.1, fun g i => ⟨m.2.1 g i, m.2.2 g i⟩⟩
  left_inv m := by
    apply Sigma.ext rfl
    apply heq_of_eq
    funext g i
    exact Sigma.eta _
  right_inv m := by rcases m with ⟨degree, primes, residues⟩; rfl

def giantSignedResidueTranslate {B : Type*} {P : B → Finset ℕ} {degree : B → ℕ}
    (primes : GiantSignedPrimeLists P degree) (d : ℤ) :
    GiantSignedResidues primes ≃ GiantSignedResidues primes :=
  Equiv.piCongrRight fun _ => Equiv.piCongrRight fun _ => Equiv.addRight (d : ZMod _)

theorem giantSignedMemoryCoordinates_translate {B : Type*} {P : B → Finset ℕ}
    (d : ℤ) (m : GiantSignedMemory P) :
    giantSignedMemoryCoordinates P (giantSignedMemoryTranslate d m) =
      ⟨m.1, (giantSignedMemoryCoordinates P m).2.1,
        giantSignedResidueTranslate (giantSignedMemoryCoordinates P m).2.1 d
          (giantSignedMemoryCoordinates P m).2.2⟩ := rfl

def giantSignedPrimeListMass {B : Type*} [Fintype B] {P : B → Finset ℕ}
    (ν : (g : B) → P g → ℝ) {degree : B → ℕ}
    (primes : GiantSignedPrimeLists P degree) : ℝ :=
  ∏ g, (∏ i, ν g (primes g i)) / (Nat.factorial (degree g) : ℝ)

theorem giantSignedMemoryMass_coordinates {B : Type*} [Fintype B] {P : B → Finset ℕ}
    (ν : (g : B) → P g → ℝ) (m : GiantSignedMemory P) :
    giantSignedMemoryMass ν m =
      giantSignedPrimeListMass ν (giantSignedMemoryCoordinates P m).2.1 := rfl

theorem giantSignedMemoryMass_at {B : Type*} [Fintype B] {P : B → Finset ℕ}
    (ν : (g : B) → P g → ℝ) (degree : B → ℕ)
    (primes : GiantSignedPrimeLists P degree) (residues : GiantSignedResidues primes) :
    giantSignedMemoryMass ν ((giantSignedMemoryCoordinates P).symm
      ⟨degree, primes, residues⟩) = giantSignedPrimeListMass ν primes := rfl

theorem giantSignedMemoryTranslate_permute {B : Type*} {P : B → Finset ℕ}
    (d : ℤ) (m : GiantSignedMemory P)
    (σ : (g : B) → Equiv.Perm (Fin (m.1 g))) :
    giantSignedMemoryTranslate d (giantSignedMemoryPermute m σ) =
      giantSignedMemoryPermute (giantSignedMemoryTranslate d m) σ := rfl

theorem GiantSignedMemorySymmetric.translate {B : Type*} {P : B → Finset ℕ}
    {f : GiantSignedMemory P → ℂ} (hf : GiantSignedMemorySymmetric f) (d : ℤ) :
    GiantSignedMemorySymmetric (fun m => f (giantSignedMemoryTranslate d m)) := by
  intro m σ
  change f (giantSignedMemoryTranslate d (giantSignedMemoryPermute m σ)) =
    f (giantSignedMemoryTranslate d m)
  rw [giantSignedMemoryTranslate_permute]
  exact hf (giantSignedMemoryTranslate d m) σ

instance giantSignedMemory_countable {B : Type*} [Fintype B] (P : B → Finset ℕ)
    [∀ (g : B) (p : P g), NeZero p.val] :
    Countable (GiantSignedMemory P) := by
  let : ∀ g, Countable (GiantSignedParticle (P g)) := fun g => by
    change Countable (Σ p : P g, ZMod p.val)
    infer_instance
  change Countable (Σ degree : B → ℕ,
    (g : B) → Fin (degree g) → GiantSignedParticle (P g))
  infer_instance

instance giantSignedResidues_fintype {B : Type*} [Fintype B] {P : B → Finset ℕ}
    [∀ (g : B) (p : P g), NeZero p.val] {degree : B → ℕ}
    (primes : GiantSignedPrimeLists P degree) : Fintype (GiantSignedResidues primes) := by
  classical
  letI : ∀ (g : B) (i : Fin (degree g)), Fintype (ZMod (primes g i).val) := fun g i => by
    let : NeZero (primes g i).val := ‹∀ (g : B) (p : P g), NeZero p.val› g (primes g i)
    infer_instance
  change Fintype ((g : B) → (i : Fin (degree g)) → ZMod (primes g i).val)
  infer_instance

end
end ArtinMatthews
