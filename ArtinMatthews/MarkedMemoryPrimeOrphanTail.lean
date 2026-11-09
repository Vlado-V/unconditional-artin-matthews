module

public import ArtinMatthews.MarkedMemoryChoiceCountTail
public import ArtinMatthews.MarkedMemoryOrphanChoiceBounds


set_option backward.privateInPublic true
@[expose] public section

/-! The exact finite prime-choice orphan tail. Active signed choices
are retained through their literal absolute mass; only the independent
inactive-prime orphan factors enter the exponential tail. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

variable {N : ℕ} {L : Type*} [DecidableEq L]

def markedMemoryPrimeOrphanCost (A : Finset (Fin (N+1)))
    (c : MarkedMemoryPrimeLifespanChoice N) : ℕ :=
  if A.Nonempty then 0 else markedMemoryOrphanChoiceCost c

def markedMemoryPrimeActiveAbsoluteMass (eta : Fin (N+1) → ℝ) (line : Fin (N+1) → L)
    (A : Finset (Fin (N+1))) (atom : ℝ) : ℝ :=
  if A.Nonempty then ∑ c : MarkedMemoryPrimeLifespanChoice N,
    |markedMemoryPrimeLifespanChoiceWeight eta line A atom c| else 1

def markedMemoryPrimeInactiveAtom (A : Finset (Fin (N+1))) (atom : ℝ) : ℝ :=
  if A.Nonempty then 0 else atom

theorem markedMemoryPrimeActiveAbsoluteMass_nonneg
    (eta : Fin (N+1) → ℝ) (line : Fin (N+1) → L)
    (A : Finset (Fin (N+1))) (atom : ℝ) :
    0 ≤ markedMemoryPrimeActiveAbsoluteMass eta line A atom := by
  unfold markedMemoryPrimeActiveAbsoluteMass
  split_ifs
  · exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  · exact zero_le_one

theorem markedMemoryPrimeOrphan_generating_le_exp
    (eta : Fin (N+1) → ℝ) (line : Fin (N+1) → L)
    (heta : ∀ v,0≤eta v ∧ eta v≤1) (A : Finset (Fin (N+1)))
    (atom r : ℝ) (ha : 0≤atom) (hr : 0≤r) :
    (∑ c : MarkedMemoryPrimeLifespanChoice N,
      r ^ markedMemoryPrimeOrphanCost A c *
        |markedMemoryPrimeLifespanChoiceWeight eta line A atom c|) ≤
      markedMemoryPrimeActiveAbsoluteMass eta line A atom *
        Real.exp (r*markedMemoryPrimeInactiveAtom A atom*((N:ℝ)+1)^2) := by
  by_cases hA : A.Nonempty
  · simp only [markedMemoryPrimeOrphanCost,hA,ite_true,pow_zero,one_mul,
      markedMemoryPrimeActiveAbsoluteMass,markedMemoryPrimeInactiveAtom,mul_zero,zero_mul,
      Real.exp_zero,mul_one,le_refl]
  · have h0 : A=∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    subst A
    have hw (c : MarkedMemoryPrimeLifespanChoice N) :
        |markedMemoryOrphanChoice eta line atom c|=markedMemoryOrphanChoice eta line atom c :=
      abs_of_nonneg (markedMemoryOrphanChoice_nonneg eta line heta atom ha c)
    simpa only [markedMemoryPrimeOrphanCost,Finset.not_nonempty_empty,ite_false,
      markedMemoryPrimeLifespanChoiceWeight,dite_false,hw,markedMemoryPrimeActiveAbsoluteMass,
      markedMemoryPrimeInactiveAtom,one_mul] using
      markedMemoryOrphanChoice_generating_le_exp eta line heta atom r ha hr

variable {I : Type*} [Fintype I] {Line : I → Type*} [∀ i,DecidableEq (Line i)]
  (eta : Fin (N+1) → ℝ) (lines : (i : I) → Fin (N+1) → Line i)
  (active : I → Finset (Fin (N+1))) (atom : I → ℝ)

def markedMemoryPrimeOrphanCount (c : I → MarkedMemoryPrimeLifespanChoice N) : ℕ :=
  ∑ i,markedMemoryPrimeOrphanCost (active i) (c i)

theorem markedMemoryPrimeOrphan_absolute_tail
    (heta : ∀ v,0≤eta v ∧ eta v≤1) (ha : ∀ i,0≤atom i)
    (r : ℝ) (hr : 1≤r) (m : ℕ) :
    (∑ c : I → MarkedMemoryPrimeLifespanChoice N,
      if m ≤ markedMemoryPrimeOrphanCount active c then
        ∏ i,|markedMemoryPrimeLifespanChoiceWeight eta (lines i) (active i) (atom i) (c i)| else 0) ≤
      (∏ i,markedMemoryPrimeActiveAbsoluteMass eta (lines i) (active i) (atom i)) *
        Real.exp (r*(∑ i,markedMemoryPrimeInactiveAtom (active i) (atom i))*((N:ℝ)+1)^2)/r^m := by
  have hr0 : 0≤r := by linarith
  have ht := markedMemoryChoiceCount_tail
    (fun i c => markedMemoryPrimeOrphanCost (active i) c)
    (fun i c => |markedMemoryPrimeLifespanChoiceWeight eta (lines i) (active i) (atom i) c|)
    (fun _ _ => abs_nonneg _) r hr m
  refine ht.trans ?_
  apply div_le_div_of_nonneg_right _ (pow_nonneg hr0 _)
  calc
    _ ≤ ∏ i,markedMemoryPrimeActiveAbsoluteMass eta (lines i) (active i) (atom i) *
        Real.exp (r*markedMemoryPrimeInactiveAtom (active i) (atom i)*((N:ℝ)+1)^2) := by
      apply Finset.prod_le_prod₀
      · intro i _
        exact Finset.sum_nonneg (fun c _ => mul_nonneg (pow_nonneg hr0 _) (abs_nonneg _))
      · intro i _
        exact markedMemoryPrimeOrphan_generating_le_exp eta (lines i) heta (active i) (atom i) r (ha i) hr0
    _ = _ := by
      rw [Finset.prod_mul_distrib,← Real.exp_sum]
      congr 2
      rw [← Finset.sum_mul,← Finset.mul_sum]

theorem markedMemoryPrimeOrphan_signed_tail
    (heta : ∀ v,0≤eta v ∧ eta v≤1) (ha : ∀ i,0≤atom i)
    (r : ℝ) (hr : 1≤r) (m : ℕ) :
    |∑ c : I → MarkedMemoryPrimeLifespanChoice N,
      if m ≤ markedMemoryPrimeOrphanCount active c then
        ∏ i,markedMemoryPrimeLifespanChoiceWeight eta (lines i) (active i) (atom i) (c i) else 0| ≤
      (∏ i,markedMemoryPrimeActiveAbsoluteMass eta (lines i) (active i) (atom i)) *
        Real.exp (r*(∑ i,markedMemoryPrimeInactiveAtom (active i) (atom i))*((N:ℝ)+1)^2)/r^m := by
  calc
    _ ≤ ∑ c : I → MarkedMemoryPrimeLifespanChoice N,
        |if m ≤ markedMemoryPrimeOrphanCount active c then
          ∏ i,markedMemoryPrimeLifespanChoiceWeight eta (lines i) (active i) (atom i) (c i) else 0| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ c : I → MarkedMemoryPrimeLifespanChoice N,
        if m ≤ markedMemoryPrimeOrphanCount active c then
          ∏ i,|markedMemoryPrimeLifespanChoiceWeight eta (lines i) (active i) (atom i) (c i)| else 0 := by
      apply Finset.sum_congr rfl
      intro c _
      split_ifs <;> simp only [Finset.abs_prod,abs_zero]
    _ ≤ _ := markedMemoryPrimeOrphan_absolute_tail eta lines active atom heta ha r hr m

end
end ArtinMatthews
