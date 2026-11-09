module

public import ArtinMatthews.GiantSignedChronologicalChoices
public import ArtinMatthews.GiantSignedEdgeMoveExpansion
public import ArtinMatthews.GiantTwoSidedResiduePathExpansion


set_option backward.privateInPublic true
@[expose] public section

/-! The literal expanded chronological term. No intermediate memory
measure is inserted into a row. The sole state measure is at the initial
boundary, and both pending half dampings occur on every edge. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] giantSignedBirthPermutationFintype

variable {S B : Type*} [Fintype S] [DecidableEq S] [Fintype B] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell n : ℕ}
    {C : Fin n → B → Finset (Fin k)} {batch : Fin (n+1) → B → ℕ}

def giantSignedChronologicalSmallProduct
    (h : GiantSignedChronologicalChoices PS PB ell C batch) (i : Fin n) : ℕ :=
  ∏ g : S, ∏ s : Fin k,
    ((giantSignedChronologicalSmallSource h i).val.2 g (Fin.castAdd ell s)).val

def giantSignedChronologicalProduct
    (h : GiantSignedChronologicalChoices PS PB ell C batch) (i : Fin n) : ℕ :=
  giantSignedChronologicalSmallProduct h i *
    (giantTwoSidedPatternCopiedProduct (C i) (giantSignedChronologicalBigSource h i) *
      giantTwoSidedPatternAuxiliaryProduct (h.auxiliary i))

def giantSignedChronologicalAuxiliaryBan
    (h : GiantSignedChronologicalChoices PS PB ell C batch) (i : Fin n) : Prop :=
  ∀ g (a : ↥(C i g)),
    (∀ j : S, ∀ s : Fin (k+ell),
      (h.auxiliary i g a).val ≠ (giantSignedChronologicalSmallSource h i).val.2 j s ∧
      (h.auxiliary i g a).val ≠ (giantSignedChronologicalSmallTarget h i).val.2 j s) ∧
    (∀ j : B, ∀ s : Fin (k+ell),
      (h.auxiliary i g a).val ≠ (giantSignedChronologicalBigSource h i j s).val ∧
      (h.auxiliary i g a).val ≠ (giantSignedChronologicalBigTarget h i j s).val)

def GiantSignedChronologicalCompatible (κ : Fin n → ℤ)
    (h : GiantSignedChronologicalChoices PS PB ell C batch) : Prop :=
  ∀ i : Fin n,
    (∀ g : S, ∀ s : Fin k,
      (giantSignedChronologicalSmallTarget h i).val.2 g (Fin.castAdd ell s) =
        (giantSignedChronologicalSmallSource h i).val.2 g (Fin.castAdd ell s)) ∧
    (giantSignedChronologicalSmallTarget h i).val.1 =
      giantTwoSidedResidueTranslate (κ i * (giantSignedChronologicalProduct h i : ℤ))
        (giantSignedChronologicalSmallSource h i).val.1 ∧
    IdealCopied (C i) (giantSignedChronologicalBigSource h i)
      (giantSignedChronologicalBigTarget h i) ∧
    (h.state i.succ).2.2 =
      giantSignedEdgeTarget (κ i * (giantSignedChronologicalProduct h i : ℤ))
        (giantSignedChronologicalGhostTarget h i.castSucc)
        (giantSignedPatternFreeLabels (C i) (giantSignedChronologicalBigSource h i))
        (h.edge i) ∧
    (∀ g, ∀ s : Fin ((h.edge i).1 g).card,
      ¬ (giantSignedEdgeSelected ((h.edge i).1 g)
        (giantSignedPatternFreeLabels (C i) (giantSignedChronologicalBigSource h i) g) s).val ∣
          giantSignedChronologicalProduct h i) ∧
    giantSignedChronologicalAuxiliaryBan h i

def GiantSignedChronologicalBoundary
    (h : GiantSignedChronologicalChoices PS PB ell C batch) : Prop :=
  (h.state 0).2.2 = giantSignedEmptyMemory PB ∧
    giantSignedChronologicalGhostTarget h (Fin.last n) = giantSignedEmptyMemory PB

omit [Fintype B] [DecidableEq B] [DecidableEq S] in
theorem giantSignedChronologicalBoundary_final_batch
    (h : GiantSignedChronologicalChoices PS PB ell C batch)
    (hb : GiantSignedChronologicalBoundary h) (g : B) : batch (Fin.last n) g = 0 := by
  have he := congrArg (fun m : GiantSignedMemory PB => m.1 g) hb.2
  change (giantSignedFixedGhostTarget (h.state (Fin.last n)).2.2 (batch (Fin.last n))
    (h.deleted (Fin.last n)) (h.born (Fin.last n))).1 g = 0 at he
  rw [giantSignedFixedGhostTarget_degree] at he
  omega

omit [Fintype B] [DecidableEq B] [DecidableEq S] in
theorem giantSignedChronologicalBoundary_initial_deletions
    (h : GiantSignedChronologicalChoices PS PB ell C batch)
    (hb : GiantSignedChronologicalBoundary h) (g : B) : h.deleted 0 g = ∅ := by
  have he := congrArg (fun m : GiantSignedMemory PB => m.1 g) hb.1
  change (h.state 0).2.2.1 g = 0 at he
  have hc := Finset.card_le_card (Finset.subset_univ (h.deleted 0 g))
  simp only [Finset.card_univ, Fintype.card_fin, he] at hc
  exact Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hc)

def giantSignedChronologicalGhostCoefficient (ν : ∀ g, PB g → ℝ)
    (V : B → ℝ) (q : Fin (n+1) → ℝ) (ρ : ℝ)
    (h : GiantSignedChronologicalChoices PS PB ell C batch) (i : Fin (n+1)) : ℂ :=
  giantSignedGhostMemoryMoveCoefficient ν
    (fun _ => ((q i / ρ^2 : ℝ) : ℂ))
    (fun g => ((-(1-q i) * V g / ρ : ℝ) : ℂ))
    (fun _ => ((-(1-q i) / ρ : ℝ) : ℂ)) (h.state i).2.2
    (giantSignedFixedGhostMove (h.state i).2.2 (batch i) (h.deleted i) (h.born i))

def giantSignedChronologicalEdgeMemoryCoefficient (ν : ∀ g, PB g → ℝ)
    (V : B → ℝ) (κ : Fin n → ℤ) (ρ : ℝ)
    (h : GiantSignedChronologicalChoices PS PB ell C batch) (i : Fin n) : ℂ :=
  giantSignedEdgeMoveCoefficient (fun g p => (ν g p : ℂ)) V ρ
    (κ i * (giantSignedChronologicalProduct h i : ℤ)) (giantSignedChronologicalProduct h i)
    (giantSignedPatternFreeLabels (C i) (giantSignedChronologicalBigSource h i))
    (giantSignedPatternFreeLabels (C i) (giantSignedChronologicalBigTarget h i))
    (giantSignedChronologicalGhostTarget h i.castSucc) (h.edge i)

def giantSignedChronologicalEdgeCoefficient (ν : ∀ g, PB g → ℝ)
    (V : B → ℝ) (κ : Fin n → ℤ) (q ρ θ : ℝ) (ζ : Fin n → ℝ)
    (K : ∀ i, GiantTwoSidedPatternCoefficient PB (C i) ell)
    (h : GiantSignedChronologicalChoices PS PB ell C batch) (i : Fin n) : ℂ :=
  (giantTwoSidedResidueSlotNormalization (J := S) (k+ell) : ℂ) *
    (giantTwoSidedResidueSlotNormalization (J := B) (k+ell) : ℂ) *
    (∏ g : S, ((bandReciprocalMass (PS g))⁻¹ : ℂ)^ell) *
    (giantTwoSidedPatternAuxiliaryMass (h.auxiliary i) : ℂ) *
    K i (giantSignedChronologicalBigSource h i) (giantSignedChronologicalBigTarget h i)
      (h.auxiliary i) *
    (giantSignedChronologicalProduct h i : ℂ)^((ζ i : ℂ)*Complex.I) *
    idealAdditivePhase (θ * (κ i : ℝ)) (giantSignedChronologicalProduct h i) *
    (giantTwoSidedResidueDamping PS (k+ell) q
      (giantSignedChronologicalSmallSource h i).val.1 : ℂ) *
    (giantTwoSidedResidueDamping PS (k+ell) q
      (giantSignedChronologicalSmallTarget h i).val.1 : ℂ) *
    giantSignedChronologicalEdgeMemoryCoefficient ν V κ ρ h i

def giantSignedChronologicalWeight (ν : ∀ g, PB g → ℝ) (V : B → ℝ)
    (κ : Fin n → ℤ) (q : ℝ) (visitQ : Fin (n+1) → ℝ) (ρ θ : ℝ)
    (ζ : Fin n → ℝ) (K : ∀ i, GiantTwoSidedPatternCoefficient PB (C i) ell)
    (h : GiantSignedChronologicalChoices PS PB ell C batch) : ℂ :=
  if GiantSignedChronologicalCompatible κ h ∧ GiantSignedChronologicalBoundary h then
    (giantSignedStateMass PS ν (h.state 0) : ℂ) *
      (∏ i, giantSignedChronologicalGhostCoefficient ν V visitQ ρ h i) *
      ∏ i, giantSignedChronologicalEdgeCoefficient ν V κ q ρ θ ζ K h i
  else 0

def giantSignedChronologicalDistinctWeight (ν : ∀ g, PB g → ℝ) (V : B → ℝ)
    (κ : Fin n → ℤ) (q : ℝ) (visitQ : Fin (n+1) → ℝ) (ρ θ : ℝ)
    (ζ : Fin n → ℝ) (K : ∀ i, GiantTwoSidedPatternCoefficient PB (C i) ell)
    (h : GiantSignedChronologicalChoices PS PB ell C batch) : ℂ :=
  if GiantSignedBirthDistinct (giantSignedChronologicalBirthData h) then
    giantSignedChronologicalWeight ν V κ q visitQ ρ θ ζ K h else 0

theorem giantSignedChronologicalDistinctWeight_permutation_sum
    (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (κ : Fin n → ℤ)
    (q : ℝ) (visitQ : Fin (n+1) → ℝ) (ρ θ : ℝ) (ζ : Fin n → ℝ)
    (K : ∀ i, GiantTwoSidedPatternCoefficient PB (C i) ell)
    (h : GiantSignedChronologicalChoices PS PB ell C batch) :
    giantSignedChronologicalDistinctWeight ν V κ q visitQ ρ θ ζ K h =
      ∑ σ : Equiv.Perm (GiantSignedBirthAddress B ell C batch),
        (σ.sign : ℂ) *
          (if GiantSignedBirthPermutationEvent (giantSignedChronologicalBirthData h) σ then
            giantSignedChronologicalWeight ν V κ q visitQ ρ θ ζ K h else 0) :=
  giantSignedBirthDistinct_weighted_sum _ _

end
end ArtinMatthews
