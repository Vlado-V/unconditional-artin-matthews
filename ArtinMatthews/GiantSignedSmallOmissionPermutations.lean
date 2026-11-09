module

public import ArtinMatthews.GiantSignedSmallOmissions


set_option backward.privateInPublic true
@[expose] public section

/-! The actual independent small-group permutations push forward to
uniform independent ell-subsets. The transfer step is absent from this index calculation. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

section Permutations
variable {S : Type*}
variable (kCopy ell : ℕ)

def giantSignedSmallOmissionSuffix : Finset (Fin (kCopy + ell)) :=
  Finset.univ.map ⟨Fin.natAdd kCopy, Fin.natAdd_injective _ _⟩

def giantSignedSmallPermutationOmission
    (σ : (g : S) → Equiv.Perm (Fin (kCopy + ell))) :
    GiantSignedSmallOmission S (kCopy + ell) ell := fun g =>
  ⟨(giantSignedSmallOmissionSuffix kCopy ell).map (σ g).toEmbedding,
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, by
      simp only [Finset.card_map, giantSignedSmallOmissionSuffix, Finset.card_univ, Fintype.card_fin]⟩⟩

def giantSignedSmallPermutationShift
    (τ : (g : S) → Equiv.Perm (Fin (kCopy + ell))) :
    ((g : S) → Equiv.Perm (Fin (kCopy + ell))) ≃
      ((g : S) → Equiv.Perm (Fin (kCopy + ell))) where
  toFun σ g := (σ g).trans (τ g)
  invFun σ g := (σ g).trans (τ g).symm
  left_inv σ := by funext g; apply Equiv.ext; intro i; simp
  right_inv σ := by funext g; apply Equiv.ext; intro i; simp

theorem giantSignedSmallPermutationOmission_shift
    (σ τ : (g : S) → Equiv.Perm (Fin (kCopy + ell))) (g : S) :
    (giantSignedSmallPermutationOmission kCopy ell
      (giantSignedSmallPermutationShift kCopy ell τ σ) g).1 =
      (giantSignedSmallPermutationOmission kCopy ell σ g).1.map (τ g).toEmbedding := by
  change (giantSignedSmallOmissionSuffix kCopy ell).map ((σ g).trans (τ g)).toEmbedding =
    ((giantSignedSmallOmissionSuffix kCopy ell).map (σ g).toEmbedding).map (τ g).toEmbedding
  rw [Finset.map_map]
  rfl

variable [Fintype S] [DecidableEq S]

theorem giantSignedSmallPermutationOmission_fiber_card_eq
    (U V : GiantSignedSmallOmission S (kCopy + ell) ell) :
    Fintype.card {σ : (g : S) → Equiv.Perm (Fin (kCopy + ell)) //
      giantSignedSmallPermutationOmission kCopy ell σ = U} =
    Fintype.card {σ : (g : S) → Equiv.Perm (Fin (kCopy + ell)) //
      giantSignedSmallPermutationOmission kCopy ell σ = V} := by
  classical
  have hex (g : S) : ∃ τ : Equiv.Perm (Fin (kCopy + ell)), (U g).1.map τ.toEmbedding = (V g).1 :=
    Equiv.Perm.exists_map_finset_eq (U g).1 (V g).1
      ((markedRawDeletionBatch_deleted_card (U g)).trans (markedRawDeletionBatch_deleted_card (V g)).symm)
  choose τ hτ using hex
  let E := giantSignedSmallPermutationShift kCopy ell τ
  have he (σ : (g : S) → Equiv.Perm (Fin (kCopy + ell))) :
      giantSignedSmallPermutationOmission kCopy ell σ = U ↔
        giantSignedSmallPermutationOmission kCopy ell (E σ) = V := by
    constructor
    · intro h
      funext g
      apply Subtype.ext
      rw [giantSignedSmallPermutationOmission_shift]
      have hg := congrArg (fun W : GiantSignedSmallOmission S (kCopy + ell) ell => (W g).1) h
      rw [hg, hτ g]
    · intro h
      funext g
      apply Subtype.ext
      apply Finset.map_injective (τ g).toEmbedding
      have hg := congrArg (fun W : GiantSignedSmallOmission S (kCopy + ell) ell => (W g).1) h
      change (giantSignedSmallPermutationOmission kCopy ell (E σ) g).1 = (V g).1 at hg
      rw [giantSignedSmallPermutationOmission_shift] at hg
      exact hg.trans (hτ g).symm
  exact Fintype.card_congr (E.subtypeEquiv he)

theorem giantSignedSmallPermutationOmission_fiber_card
    (U : GiantSignedSmallOmission S (kCopy + ell) ell) :
    Fintype.card {σ : (g : S) → Equiv.Perm (Fin (kCopy + ell)) //
      giantSignedSmallPermutationOmission kCopy ell σ = U} =
        (ell.factorial * kCopy.factorial) ^ Fintype.card S := by
  classical
  let f := giantSignedSmallPermutationOmission (S := S) kCopy ell
  let N := Fintype.card {σ : (g : S) → Equiv.Perm (Fin (kCopy + ell)) // f σ = U}
  have hc (V : GiantSignedSmallOmission S (kCopy + ell) ell) :
      Fintype.card {σ : (g : S) → Equiv.Perm (Fin (kCopy + ell)) // f σ = V} = N :=
    giantSignedSmallPermutationOmission_fiber_card_eq kCopy ell V U
  have hsum := Fintype.card_congr (Equiv.sigmaFiberEquiv f)
  rw [Fintype.card_sigma] at hsum
  have htotal : Fintype.card (GiantSignedSmallOmission S (kCopy + ell) ell) * N =
      Fintype.card ((g : S) → Equiv.Perm (Fin (kCopy + ell))) := by
    simpa only [hc, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id] using hsum
  have hG : Fintype.card ((g : S) → Equiv.Perm (Fin (kCopy + ell))) =
      (kCopy + ell).factorial ^ Fintype.card S := by
    simp only [Fintype.card_pi, Fintype.card_perm, Fintype.card_fin, Finset.prod_const,
      Finset.card_univ]
  have hf := Nat.choose_mul_factorial_mul_factorial (show ell ≤ kCopy + ell by omega)
  have hbase : (kCopy + ell).choose ell * (ell.factorial * kCopy.factorial) =
      (kCopy + ell).factorial := by
    simpa only [Nat.add_sub_cancel_right, Nat.mul_assoc] using hf
  have hfactor : Fintype.card (GiantSignedSmallOmission S (kCopy + ell) ell) *
      ((ell.factorial * kCopy.factorial) ^ Fintype.card S) =
        Fintype.card ((g : S) → Equiv.Perm (Fin (kCopy + ell))) := by
    rw [giantSignedSmallOmission_card, giantSignedSmallOmissionNumber, hG, ← mul_pow, hbase]
  have hpos : 0 < Fintype.card (GiantSignedSmallOmission S (kCopy + ell) ell) := by
    rw [giantSignedSmallOmission_card]
    exact giantSignedSmallOmissionNumber_pos S kCopy ell
  exact Nat.eq_of_mul_eq_mul_left hpos (htotal.trans hfactor.symm)

theorem giantSignedSmallPermutationOmission_sum {K : Type*} [Semiring K]
    (F : GiantSignedSmallOmission S (kCopy + ell) ell → K) :
    (∑ σ : (g : S) → Equiv.Perm (Fin (kCopy + ell)),
      F (giantSignedSmallPermutationOmission kCopy ell σ)) =
        ((ell.factorial * kCopy.factorial : ℕ) : K) ^ Fintype.card S * ∑ U, F U := by
  classical
  let f := giantSignedSmallPermutationOmission (S := S) kCopy ell
  rw [← Equiv.sum_comp (Equiv.sigmaFiberEquiv f), Fintype.sum_sigma, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro U _
  calc
    _ = ∑ _σ : {σ : (g : S) → Equiv.Perm (Fin (kCopy + ell)) // f σ = U}, F U := by
      apply Finset.sum_congr rfl
      intro σ _
      exact congrArg F σ.property
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      have hc : Fintype.card {σ : (g : S) → Equiv.Perm (Fin (kCopy + ell)) // f σ = U} =
          (ell.factorial * kCopy.factorial) ^ Fintype.card S :=
        giantSignedSmallPermutationOmission_fiber_card kCopy ell U
      rw [hc, Nat.cast_pow]

theorem giantSignedSmallPermutationOmission_average {K : Type*} [Field K]
    [CharZero K] (F : GiantSignedSmallOmission S (kCopy + ell) ell → K) :
    (∑ σ : (g : S) → Equiv.Perm (Fin (kCopy + ell)),
      F (giantSignedSmallPermutationOmission kCopy ell σ)) /
        ((kCopy + ell).factorial : K) ^ Fintype.card S =
      (∑ U, F U) / (giantSignedSmallOmissionNumber S (kCopy + ell) ell : K) := by
  have hf := Nat.choose_mul_factorial_mul_factorial (show ell ≤ kCopy + ell by omega)
  have hbase : (kCopy + ell).choose ell * (ell.factorial * kCopy.factorial) =
      (kCopy + ell).factorial := by
    simpa only [Nat.add_sub_cancel_right, Nat.mul_assoc] using hf
  have hdenNat : giantSignedSmallOmissionNumber S (kCopy + ell) ell *
      (ell.factorial * kCopy.factorial) ^ Fintype.card S =
        (kCopy + ell).factorial ^ Fintype.card S := by
    rw [giantSignedSmallOmissionNumber, ← mul_pow, hbase]
  have hden : (giantSignedSmallOmissionNumber S (kCopy + ell) ell : K) *
      ((ell.factorial * kCopy.factorial : ℕ) : K) ^ Fintype.card S =
        ((kCopy + ell).factorial : K) ^ Fintype.card S := by exact_mod_cast hdenNat
  have hfac : (((ell.factorial * kCopy.factorial : ℕ) : K) ^ Fintype.card S) ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)))
  have hnum : (giantSignedSmallOmissionNumber S (kCopy + ell) ell : K) ≠ 0 :=
    Nat.cast_ne_zero.mpr (giantSignedSmallOmissionNumber_pos S kCopy ell).ne'
  rw [giantSignedSmallPermutationOmission_sum, ← hden]
  field_simp [hfac, hnum]

end Permutations
end
end ArtinMatthews
