module

public import ArtinMatthews.MarkedMinorArcRawMemoryBulkAppend
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Finset.Powerset


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine unordered-batch Fock factorial integration from the actual old
index subsets. The birth 1/d! and survivor 1/n! arise from finite counting;
no adjacency, row bound or memory operator norm is assumed. -/
namespace ArtinMatthews
open scoped BigOperators

abbrev MarkedRawDeletionBatch (k d : ℕ) :=
  ↥((Finset.univ : Finset (Fin k)).powersetCard d)

theorem markedRawDeletionBatch_card (k d : ℕ) :
    Fintype.card (MarkedRawDeletionBatch k d)=k.choose d := by
  simp only [MarkedRawDeletionBatch,Fintype.card_coe,Finset.card_powersetCard,
    Finset.card_univ,Fintype.card_fin]

theorem markedRawDeletionBatch_deleted_card {k d : ℕ} (S : MarkedRawDeletionBatch k d) :
    S.1.card=d := (Finset.mem_powersetCard.mp S.2).2

theorem markedRawDeletionBatch_survivor_card {k n d : ℕ} (hk : n+d=k)
    (S : MarkedRawDeletionBatch k d) : (S.1ᶜ).card=n := by
  have hh := markedRawSubsetIndex_card S.1
  have hd := markedRawDeletionBatch_deleted_card S
  omega

/-- Exact unordered-batch deletion/creation pairing for symmetric actual
old particle functions. It retains every repeated particle value and all
actual indexed deletion choices. -/
theorem markedRawMemory_factorial_batch_delete {X : Type*} [Fintype X]
    {k n d : ℕ} (hk : n+d=k) (μ : X → ℂ) (g : (Fin k → X) → ℂ)
    (hg : MarkedRawTupleSymmetric k g) (f : (Fin d → X) → (Fin n → X) → ℂ) :
    (∑ a : Fin k → X, ((∏ i, μ (a i))/(Nat.factorial k : ℂ))*g a*
      ∑ S : MarkedRawDeletionBatch k d,
        f (markedRawDeletedTupleCast S.1 (markedRawDeletionBatch_deleted_card S) a)
          (markedRawSurvivorTupleCast S.1 (markedRawDeletionBatch_survivor_card hk S) a))=
      ∑ deleted : Fin d → X, ∑ survivors : Fin n → X,
        ((∏ i, μ (deleted i))*(∏ i, μ (survivors i)))/
          ((Nat.factorial d : ℂ)*(Nat.factorial n : ℂ))*
          g (fun i => Fin.addCases survivors deleted (Fin.cast hk.symm i))*f deleted survivors := by
  classical
  let R : ℂ := ∑ deleted : Fin d → X, ∑ survivors : Fin n → X,
    (∏ i, μ (deleted i))*(∏ i, μ (survivors i))*
      g (fun i => Fin.addCases survivors deleted (Fin.cast hk.symm i))*f deleted survivors
  have hkd : d ≤ k := by omega
  have hkn : k-d=n := by omega
  have hfac : (k.choose d : ℂ)*(Nat.factorial d : ℂ)*(Nat.factorial n : ℂ)=(Nat.factorial k : ℂ) := by
    have hh := Nat.choose_mul_factorial_mul_factorial hkd
    rw [hkn] at hh
    exact_mod_cast hh
  have hfack : (Nat.factorial k : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hfacd : (Nat.factorial d : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero d
  have hfacn : (Nat.factorial n : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  calc
    _ = ∑ S : MarkedRawDeletionBatch k d,
        (∑ a : Fin k → X, (∏ i, μ (a i))*g a*
          f (markedRawDeletedTupleCast S.1 (markedRawDeletionBatch_deleted_card S) a)
            (markedRawSurvivorTupleCast S.1 (markedRawDeletionBatch_survivor_card hk S) a))/
          (Nat.factorial k : ℂ) := by
      simp only [div_eq_mul_inv,Finset.mul_sum,Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro S _
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = ∑ _S : MarkedRawDeletionBatch k d, R/(Nat.factorial k : ℂ) := by
      apply Finset.sum_congr rfl
      intro S _
      rw [markedRawMemory_subset_fixed_degree_integral hk S.1
        (markedRawDeletionBatch_deleted_card S) (markedRawDeletionBatch_survivor_card hk S) μ g hg f]
    _ = (k.choose d : ℂ)*R/(Nat.factorial k : ℂ) := by
      simp only [Finset.sum_const,Finset.card_univ,markedRawDeletionBatch_card,nsmul_eq_mul]
      ring
    _ = R/((Nat.factorial d : ℂ)*(Nat.factorial n : ℂ)) := by
      apply (div_eq_div_iff hfack (mul_ne_zero hfacd hfacn)).mpr
      linear_combination R*hfac
    _ = _ := by
      dsimp only [R]
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro deleted _
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro survivors _
      ring

end ArtinMatthews
