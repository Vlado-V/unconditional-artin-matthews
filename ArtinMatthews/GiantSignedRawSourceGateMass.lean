module

public import ArtinMatthews.GiantSignedRawRareGates
public import ArtinMatthews.GiantSignedRawAveraging
public import ArtinMatthews.GiantSignedStateMemoryCutoff


set_option backward.privateInPublic true
@[expose] public section

/-! The literal outer law retains the small-permutation rare-gate mass. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell : ℕ} {C : B → Finset (Fin k)}

def giantSignedRawMoveOuter {m : GiantSignedMemory PB}
    (r : GiantSignedRawEdgeMove PS PB ell C m) : GiantSignedRawOuterChoice (S := S) PB C ell :=
  ((r.sourceSmallPermutation, r.sourceBigPermutation),
    (r.targetSmallPermutation, r.targetBigPermutation), r.auxiliary)

def GiantSignedRawOuterSourceGate (κ : ℤ) (s : GiantSignedState PS PB (k+ell))
    (i : GiantSignedRawOuterChoice (S := S) PB C ell) : Prop :=
  GiantSignedSmallSourceMemoryAllows s.1.val.2 κ
    (giantTwoSidedPatternCopiedProduct C (giantSignedGroupedTuplePermutation i.1.2 s.2.1) *
      giantTwoSidedPatternAuxiliaryProduct i.2.2) s.2.2 i.1.1

omit [DecidableEq S] [DecidableEq B] in
theorem giantSignedRawSourceRareGate_outer (κ : ℤ) (s : GiantSignedState PS PB (k+ell))
    (r : GiantSignedRawEdgeMove PS PB ell C s.2.2) :
    GiantSignedRawSourceRareGate κ s r ↔
      GiantSignedRawOuterSourceGate κ s (giantSignedRawMoveOuter r) := Iff.rfl

theorem giantSignedRawOuterSourceGate_mass
    (hPS : ∀ g p, p ∈ PS g → p.Prime) (hPB : ∀ g p, p ∈ PB g → p.Prime)
    (hdis : Pairwise (fun g h => Disjoint (PS g) (PS h)))
    (hsep : ∀ g h, Disjoint (PS g) (PB h))
    (hVB : ∀ g, 0 < bandReciprocalMass (PB g))
    (s : GiantSignedState PS PB (k+ell))
    (N : ℕ) (hN : (∑ g, s.2.2.1 g) ≤ N)
    (kStep : ℕ) (hk : 0 < kStep) (sign : ℤ) (hsign : sign = 1 ∨ sign = -1)
    (hstep : ∀ g i, kStep < (s.2.2.2 g i).1.val)
    (tSmall tBig : ℝ) (hlabels : ∀ g i, (s.1.val.2 g i : ℝ) ≤ Real.exp tSmall)
    (hbudget : (ell : ℝ) * (Fintype.card S : ℝ) * tSmall < tBig)
    (hlower : ∀ g i, Real.exp tBig ≤ ((s.2.2.2 g i).1.val : ℝ)) :
    (∑ i : GiantSignedRawOuterChoice (S := S) PB C ell,
      if GiantSignedRawOuterSourceGate (sign * kStep) s i then giantSignedRawOuterWeight i else 0) ≤
      (N : ℝ) / (giantSignedSmallOmissionNumber S (k+ell) ell : ℝ) := by
  let A := S → Equiv.Perm (Fin (k+ell))
  let T := (B → Equiv.Perm (Fin (k+ell))) ×
    (GiantSignedStateSlotPermutations S B (k+ell) × GiantTwoSidedPatternAuxiliary PB C)
  let e : GiantSignedRawOuterChoice (S := S) PB C ell ≃ A × T := Equiv.prodAssoc _ _ _
  let ε : ℝ := (N : ℝ) / (giantSignedSmallOmissionNumber S (k+ell) ell : ℝ)
  let w : T → ℝ := fun t => giantSignedRawOuterWeight (e.symm (fun _ => Equiv.refl _, t))
  have hw (t : T) : 0 ≤ w t := giantSignedRawOuterWeight_nonneg hVB _
  have he (a : A) (t : T) : giantSignedRawOuterWeight (e.symm (a,t)) = w t := rfl
  have hcount (t : T) :
      (∑ a : A, if GiantSignedRawOuterSourceGate (sign * kStep) s (e.symm (a,t))
        then (1 : ℝ) else 0) ≤ ε * (Fintype.card A : ℝ) := by
    have hp := giantSignedSmallRareTransfer_source_bound hPS hPB hdis hsep
      s.1.val.2 s.1.property.1 kStep hk sign hsign
      (giantTwoSidedPatternCopiedProduct C (giantSignedGroupedTuplePermutation t.1 s.2.1) *
        giantTwoSidedPatternAuxiliaryProduct t.2.2) s.2.2 N hN hstep tSmall tBig hlabels hbudget hlower
    have hd : 0 < ((k+ell).factorial : ℝ) ^ Fintype.card S :=
      pow_pos (Nat.cast_pos.mpr (Nat.factorial_pos _)) _
    have hcard : (Fintype.card A : ℝ) = ((k+ell).factorial : ℝ) ^ Fintype.card S := by
      simp only [A, Fintype.card_pi, Fintype.card_perm, Fintype.card_fin, Finset.prod_const,
        Finset.card_univ, Nat.cast_pow]
    rw [hcard]
    exact (div_le_iff₀ hd).mp hp
  have hfiber (t : T) :
      (∑ a : A, w t * (if GiantSignedRawOuterSourceGate (sign * kStep) s (e.symm (a,t))
        then (1 : ℝ) else 0)) ≤ ε * ∑ _a : A, w t := by
    rw [← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    calc
      _ ≤ w t * (ε * (Fintype.card A : ℝ)) := mul_le_mul_of_nonneg_left (hcount t) (hw t)
      _ = _ := by ring
  have hleft :
      (∑ i : GiantSignedRawOuterChoice (S := S) PB C ell,
        if GiantSignedRawOuterSourceGate (sign * kStep) s i then giantSignedRawOuterWeight i else 0) =
      ∑ t : T, ∑ a : A, w t *
        (if GiantSignedRawOuterSourceGate (sign * kStep) s (e.symm (a,t)) then (1 : ℝ) else 0) := by
    rw [← e.symm.sum_comp]
    simp only [Fintype.sum_prod_type, he, mul_ite, mul_one, mul_zero]
    exact Finset.sum_comm
  have htotal :
      (∑ i : GiantSignedRawOuterChoice (S := S) PB C ell, giantSignedRawOuterWeight i) =
        ∑ t : T, ∑ _a : A, w t := by
    rw [← e.symm.sum_comp]
    simp only [Fintype.sum_prod_type, he]
    exact Finset.sum_comm
  calc
    _ = _ := hleft
    _ ≤ ∑ t : T, ε * ∑ _a : A, w t := Finset.sum_le_sum (fun t _ => hfiber t)
    _ = ε * ∑ t : T, ∑ _a : A, w t := (Finset.mul_sum _ _ _).symm
    _ = ε * ∑ i : GiantSignedRawOuterChoice (S := S) PB C ell, giantSignedRawOuterWeight i := by rw [htotal]
    _ = ε := by rw [giantSignedRawOuterWeight_sum C hVB, mul_one]


def GiantSignedRawOuterCappedSourceGate (N : ℕ) (κ : ℤ)
    (s : GiantSignedState PS PB (k+ell))
    (i : GiantSignedRawOuterChoice (S := S) PB C ell) : Prop :=
  (∑ g, s.2.2.1 g) ≤ N ∧ GiantSignedRawOuterSourceGate κ s i

theorem giantSignedRawOuterCappedSourceGate_mass
    (hPS : ∀ g p, p ∈ PS g → p.Prime) (hPB : ∀ g p, p ∈ PB g → p.Prime)
    (hdis : Pairwise (fun g h => Disjoint (PS g) (PS h)))
    (hsep : ∀ g h, Disjoint (PS g) (PB h))
    (hVB : ∀ g, 0 < bandReciprocalMass (PB g))
    (N : ℕ) (kStep : ℕ) (hk : 0 < kStep) (sign : ℤ) (hsign : sign = 1 ∨ sign = -1)
    (hstep : ∀ g p, p ∈ PB g → kStep < p)
    (tSmall tBig : ℝ) (hlabels : ∀ g p, p ∈ PS g → (p : ℝ) ≤ Real.exp tSmall)
    (hbudget : (ell : ℝ) * (Fintype.card S : ℝ) * tSmall < tBig)
    (hlower : ∀ g p, p ∈ PB g → Real.exp tBig ≤ (p : ℝ))
    (s : GiantSignedState PS PB (k+ell)) :
    (∑ i : GiantSignedRawOuterChoice (S := S) PB C ell,
      if GiantSignedRawOuterCappedSourceGate N (sign * kStep) s i then
        giantSignedRawOuterWeight i else 0) ≤
      (N : ℝ) / (giantSignedSmallOmissionNumber S (k+ell) ell : ℝ) := by
  by_cases hs : (∑ g, s.2.2.1 g) ≤ N
  · simpa only [GiantSignedRawOuterCappedSourceGate, hs, true_and] using
      giantSignedRawOuterSourceGate_mass hPS hPB hdis hsep hVB s N hs kStep hk sign hsign
        (fun g i => hstep g _ (s.2.2.2 g i).1.property) tSmall tBig
        (fun g i => hlabels g _ (s.1.val.2 g i).property) hbudget
        (fun g i => hlower g _ (s.2.2.2 g i).1.property)
  · simp only [GiantSignedRawOuterCappedSourceGate, hs, false_and, ite_false,
      Finset.sum_const_zero]
    exact div_nonneg (Nat.cast_nonneg N) (Nat.cast_nonneg _)

end
end ArtinMatthews
