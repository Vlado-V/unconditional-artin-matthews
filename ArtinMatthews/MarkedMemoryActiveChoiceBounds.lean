module

public import ArtinMatthews.MarkedMemoryPrimeOrphanTail


set_option backward.privateInPublic true
@[expose] public section

/-! Direct absolute bounds for the actual optional active-lifespan
choices. Each prefix, interior and suffix damping product is retained
and bounded from its eta factors in the unit interval. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

variable {N : ℕ} {L : Type*} [DecidableEq L]
  (eta : Fin (N+1) → ℝ) (line : Fin (N+1) → L)
  (heta : ∀ v,0≤eta v ∧ eta v≤1)

include heta in
theorem markedMemoryDampingProduct_bounds (S : Finset (Fin (N+1))) (a : L) :
    0≤∏ v∈S,(1-eta v*markedLineHit line v a) ∧
      (∏ v∈S,(1-eta v*markedLineHit line v a))≤1 :=
  ⟨Finset.prod_nonneg (fun v _ => (markedMemoryOrphanDamping_bounds eta line heta v a).1),
    Finset.prod_le_one₀
      (fun v _ => (markedMemoryOrphanDamping_bounds eta line heta v a).1)
      (fun v _ => (markedMemoryOrphanDamping_bounds eta line heta v a).2)⟩

include heta in
theorem markedMemoryNegativeEndpoint_abs_le_one
    (v : Fin (N+1)) (a : L) (S : Finset (Fin (N+1))) :
    |-eta v*markedLineHit line v a*(∏ j∈S,(1-eta j*markedLineHit line j a))|≤1 := by
  have hd := markedMemoryDampingProduct_bounds eta line heta S a
  have hh : 0 ≤ (markedLineHit line v a:ℝ) ∧ (markedLineHit line v a:ℝ)≤1 := by
    unfold markedLineHit
    split_ifs <;> constructor <;> norm_num
  have he0 : 0≤eta v*markedLineHit line v a := mul_nonneg (heta v).1 hh.1
  have he1 : eta v*markedLineHit line v a≤1 :=
    (mul_le_mul_of_nonneg_left hh.2 (heta v).1).trans (by simpa using (heta v).2)
  have hp0 : 0≤eta v*markedLineHit line v a*(∏ j∈S,(1-eta j*markedLineHit line j a)) :=
    mul_nonneg he0 hd.1
  have hp1 : eta v*markedLineHit line v a*(∏ j∈S,(1-eta j*markedLineHit line j a))≤1 :=
    (mul_le_mul_of_nonneg_left hd.2 he0).trans (by simpa using he1)
  rw [show -eta v*markedLineHit line v a*(∏ j∈S,(1-eta j*markedLineHit line j a))=
    -(eta v*markedLineHit line v a*(∏ j∈S,(1-eta j*markedLineHit line j a))) by ring,
    abs_neg,abs_of_nonneg hp0]
  exact hp1

include heta in
theorem markedMemoryPrefixChoice_abs_le_one (a : Fin (N+1)) (c : Option (Fin (N+1))) :
    |markedMemoryPrefixChoice eta line a c|≤1 := by
  cases c with
  | none => norm_num [markedMemoryPrefixChoice]
  | some h =>
    change |if h<a then -eta h*markedLineHit line h (line a)*
      (∏ j∈Finset.univ.filter (fun j => h<j ∧ j<a),(1-eta j*markedLineHit line j (line a))) else 0|≤1
    by_cases hh : h<a
    · simp only [hh,ite_true]
      exact markedMemoryNegativeEndpoint_abs_le_one eta line heta h (line a) _
    · simp only [hh,ite_false,abs_zero,zero_le_one]

include heta in
theorem markedMemorySuffixChoice_abs_le_one (a b : Fin (N+1)) (c : Option (Fin (N+1))) :
    |markedMemorySuffixChoice eta line a b c|≤1 := by
  cases c with
  | none => norm_num [markedMemorySuffixChoice]
  | some h =>
    change |if b<h then -eta h*markedLineHit line h (line a)*
      (∏ j∈Finset.univ.filter (fun j => b<j ∧ j<h),(1-eta j*markedLineHit line j (line a))) else 0|≤1
    by_cases hh : b<h
    · simp only [hh,ite_true]
      exact markedMemoryNegativeEndpoint_abs_le_one eta line heta h (line a) _
    · simp only [hh,ite_false,abs_zero,zero_le_one]

include heta in
theorem markedMemoryActiveChoice_abs_le_atom
    (A : Finset (Fin (N+1))) (hA : A.Nonempty) (atom : ℝ) (ha : 0≤atom)
    (c : MarkedMemoryPrimeLifespanChoice N) :
    |markedMemoryPrimeLifespanChoiceWeight eta line A atom c|≤atom := by
  have hp := markedMemoryPrefixChoice_abs_le_one eta line heta (A.min' hA) c.1
  have hs := markedMemorySuffixChoice_abs_le_one eta line heta (A.min' hA) (A.max' hA) c.2
  have hd := markedMemoryDampingProduct_bounds eta line heta
    (markedMemoryInternal A (A.min' hA) (A.max' hA)) (line (A.min' hA))
  have hdabs : |markedMemoryInternalDamping A eta line (A.min' hA) (A.max' hA)|≤1 := by
    simpa only [markedMemoryInternalDamping,abs_of_nonneg hd.1] using hd.2
  unfold markedMemoryPrimeLifespanChoiceWeight
  rw [dite_eq_left hA]
  split_ifs
  · rw [abs_mul,abs_of_nonneg ha,abs_mul,abs_mul]
    calc
      _ ≤ atom*(1*1*1) := by gcongr
      _ = atom := by ring
  · simp only [mul_zero,abs_zero,ha]

include heta in
theorem markedMemoryPrimeActiveAbsoluteMass_bound
    (A : Finset (Fin (N+1))) (atom : ℝ) (ha0 : 0≤atom) (ha1 : atom≤1) :
    markedMemoryPrimeActiveAbsoluteMass eta line A atom≤((N:ℝ)+2)^2 := by
  by_cases hA : A.Nonempty
  · simp only [markedMemoryPrimeActiveAbsoluteMass,hA,ite_true]
    calc
      _ ≤ ∑ _c : MarkedMemoryPrimeLifespanChoice N,(1:ℝ) :=
        Finset.sum_le_sum (fun c _ => (markedMemoryActiveChoice_abs_le_atom eta line heta A hA atom ha0 c).trans ha1)
      _ = _ := by simp [Fintype.card_prod,Fintype.card_option]; ring
  · simp only [markedMemoryPrimeActiveAbsoluteMass,hA,ite_false]
    nlinarith [Nat.cast_nonneg N (α := ℝ)]

end
end ArtinMatthews
