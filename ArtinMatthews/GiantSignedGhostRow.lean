module

public import ArtinMatthews.GiantSignedMemoryState
public import ArtinMatthews.MarkedMinorArcRawMemoryBulkFactorial
public import Mathlib.Analysis.SpecialFunctions.Exponential


set_option backward.privateInPublic true
@[expose] public section

/-! The actual indexed ghost row deletes only old zero residues, then
appends the ordered fresh zero-residue batch. Numerical coincidences are retained. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

abbrev GiantSignedGroupMemory (P : Finset ℕ) := Σ n : ℕ, Fin n → GiantSignedParticle P

instance giantSignedParticle_fintype (P : Finset ℕ) [∀ p : P, NeZero p.val] :
    Fintype (GiantSignedParticle P) := by
  classical
  letI : ∀ p : P, Fintype (ZMod p.val) := fun p => by
    let : NeZero p.val := ‹∀ p : P, NeZero p.val› p
    infer_instance
  change Fintype (Σ p : P, ZMod p.val)
  infer_instance

def giantSignedGhostZeroIndices {P : Finset ℕ} (m : GiantSignedGroupMemory P) :
    Finset (Fin m.1) := by
  classical
  exact Finset.univ.filter (fun i => (m.2 i).2 = 0)

def giantSignedGhostTarget {P : Finset ℕ} (m : GiantSignedGroupMemory P)
    (deleted : Finset (Fin m.1)) {b : ℕ} (born : Fin b → P) : GiantSignedGroupMemory P :=
  ⟨(deletedᶜ).card + b,
    Fin.append (markedRawSubsetTupleEquiv deleted m.2).2 (fun i => ⟨born i, 0⟩)⟩

theorem giantSignedGhostTarget_degree {P : Finset ℕ} (m : GiantSignedGroupMemory P)
    (deleted : Finset (Fin m.1)) {b : ℕ} (born : Fin b → P) :
    (giantSignedGhostTarget m deleted born).1 = m.1 - deleted.card + b := by
  classical
  change (deletedᶜ).card + b = _
  rw [Finset.card_compl, Fintype.card_fin]

theorem giantSignedGhostTarget_survivor {P : Finset ℕ} (m : GiantSignedGroupMemory P)
    (deleted : Finset (Fin m.1)) {b : ℕ} (born : Fin b → P) (i : Fin (deletedᶜ).card) :
    (giantSignedGhostTarget m deleted born).2 (Fin.castAdd b i) =
      m.2 ((deletedᶜ).orderEmbOfFin rfl i) := by
  simp only [giantSignedGhostTarget, Fin.append_left, markedRawSubsetTupleEquiv_survivor]

theorem giantSignedGhostTarget_born {P : Finset ℕ} (m : GiantSignedGroupMemory P)
    (deleted : Finset (Fin m.1)) {b : ℕ} (born : Fin b → P) (i : Fin b) :
    (giantSignedGhostTarget m deleted born).2 (Fin.natAdd (deletedᶜ).card i) =
      ⟨born i, 0⟩ := by
  simp only [giantSignedGhostTarget, Fin.append_right]

def giantSignedGhostGroupApply {P : Finset ℕ} (ν : P → ℝ)
    (A C D : ℂ) (f : GiantSignedGroupMemory P → ℂ) (m : GiantSignedGroupMemory P) : ℂ :=
  ∑ deleted ∈ (giantSignedGhostZeroIndices m).powerset,
    D ^ deleted.card * A ^ ((giantSignedGhostZeroIndices m).card - deleted.card) *
      ∑' b : ℕ, (C ^ b / (Nat.factorial b : ℂ)) *
        ∑ born : Fin b → P, (∏ i, (ν (born i) : ℂ)) * f (giantSignedGhostTarget m deleted born)

def giantSignedGhostGroup {P : Finset ℕ} (ν : P → ℝ) (V q ρ : ℝ)
    (f : GiantSignedGroupMemory P → ℂ) : GiantSignedGroupMemory P → ℂ :=
  giantSignedGhostGroupApply ν ((q / ρ ^ 2 : ℝ) : ℂ)
    ((-(1-q) * V / ρ : ℝ) : ℂ) ((-(1-q) / ρ : ℝ) : ℂ) f

theorem giantSignedGhost_birthMass {P : Finset ℕ} (ν : P → ℝ) (b : ℕ) :
    (∑ born : Fin b → P, ∏ i, ν (born i)) = (∑ p : P, ν p) ^ b :=
  (Fintype.sum_pow ν b).symm

theorem giantSignedGhost_degree_weight {P : Finset ℕ} (m : GiantSignedGroupMemory P)
    (deleted : Finset (Fin m.1)) {b : ℕ} (born : Fin b → P)
    {v : ℝ} (hv : v ≠ 0) :
    v ^ (giantSignedGhostTarget m deleted born).1 / v ^ m.1 = v ^ b / v ^ deleted.card := by
  rw [giantSignedGhostTarget_degree]
  apply (div_eq_div_iff (pow_ne_zero _ hv) (pow_ne_zero _ hv)).mpr
  rw [← pow_add, ← pow_add]
  congr 1
  have hc : deleted.card ≤ m.1 := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_le_card (Finset.subset_univ deleted)
  omega

end
end ArtinMatthews
