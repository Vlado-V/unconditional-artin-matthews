module

public import ArtinMatthews.MarkedTypeIIMemory
public import ArtinMatthews.MarkedMemoryTiltBasic
public import ArtinMatthews.MarkedRootProjectiveRootLift


set_option backward.privateInPublic true
@[expose] public section

/-! Exact finite primewise factor for a nonempty active-visit set. Active
line coincidence is explicit; inactive visits and their damping are kept
at their literal indices. -/
noncomputable section
open scoped BigOperators
namespace ArtinMatthews
attribute [local instance] Classical.propDecidable

def markedMemoryActiveVisits {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M N : ℕ}
    (a : Fin (N+1) → MarkedRawActive P M) (p : Nat.Primes) : Finset (Fin (N+1)) :=
  Finset.univ.filter (fun t => ∃ j k, (a t j k).1 = p)

def MarkedMemoryActiveCoherent {N : ℕ} {Λ : Type*}
    (A : Finset (Fin (N+1))) (line : Fin (N+1) → Λ) (a : Fin (N+1)) : Prop :=
  ∀ j ∈ A, line j = line a

def markedMemoryPrimeFactor {N : ℕ} {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (A : Finset (Fin (N+1))) (η : Fin (N+1) → ℝ) (line : Fin (N+1) → Λ) : ℝ :=
  (∑ ℓ : Λ, (∏ j ∈ A, markedLineHit line j ℓ) *
    ∏ j ∈ Finset.univ \ A, (1-η j*markedLineHit line j ℓ)) / Fintype.card Λ

theorem markedMemory_active_hit_product {N : ℕ} {Λ : Type*} [DecidableEq Λ]
    (A : Finset (Fin (N+1))) (line : Fin (N+1) → Λ) (a : Fin (N+1)) :
    (∏ j ∈ A, (markedLineHit line j (line a) : ℝ)) =
      if MarkedMemoryActiveCoherent A line a then 1 else 0 := by
  classical
  by_cases hc : MarkedMemoryActiveCoherent A line a
  · rw [ite_eq_left hc]
    apply Finset.prod_eq_one
    intro j hj
    simp only [markedLineHit, hc j hj, ite_true]
  · rw [ite_eq_right hc]
    obtain ⟨j, hj, hja⟩ : ∃ j ∈ A, line j ≠ line a := by
      simpa only [MarkedMemoryActiveCoherent, not_forall, exists_prop] using hc
    apply Finset.prod_eq_zero hj
    simp only [markedLineHit, ite_eq_right (Ne.symm hja)]

/-- A nonempty active set forces its single common line. If any active
line disagrees, the primewise factor is zero; this test is never dropped. -/
theorem markedMemoryPrimeFactor_active {N : ℕ} {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (A : Finset (Fin (N+1))) (η : Fin (N+1) → ℝ) (line : Fin (N+1) → Λ)
    (a : Fin (N+1)) (ha : a ∈ A) :
    markedMemoryPrimeFactor A η line =
      (1 / (Fintype.card Λ : ℝ)) *
        (if MarkedMemoryActiveCoherent A line a then
          ∏ j ∈ Finset.univ \ A, (1-η j*markedLineHit line j (line a)) else 0) := by
  classical
  have hz (ℓ : Λ) (hℓ : ℓ ≠ line a) : (∏ j ∈ A, (markedLineHit line j ℓ : ℝ)) = 0 := by
    apply Finset.prod_eq_zero ha
    simp only [markedLineHit, ite_eq_right hℓ]
  unfold markedMemoryPrimeFactor
  rw [Finset.sum_eq_single (line a)]
  · rw [markedMemory_active_hit_product]
    split_ifs <;> ring
  · intro ℓ _ hℓ
    rw [hz ℓ hℓ, zero_mul]
  · simp

def markedMemoryBefore (N : ℕ) (a : Fin (N+1)) : Finset (Fin (N+1)) :=
  Finset.univ.filter (fun j => j<a)

def markedMemoryInternal {N : ℕ} (A : Finset (Fin (N+1))) (a c : Fin (N+1)) : Finset (Fin (N+1)) :=
  Finset.univ.filter (fun j => a<j ∧ j<c ∧ j∉A)

def markedMemoryAfter (N : ℕ) (c : Fin (N+1)) : Finset (Fin (N+1)) :=
  Finset.univ.filter (fun j => c<j)

theorem markedMemory_inactive_partition {N : ℕ} (A : Finset (Fin (N+1))) (hA : A.Nonempty) :
    Finset.univ \ A = (markedMemoryBefore N (A.min' hA) ∪
      markedMemoryInternal A (A.min' hA) (A.max' hA)) ∪ markedMemoryAfter N (A.max' hA) := by
  ext j
  have hamin := A.min'_mem hA
  have hcmax := A.max'_mem hA
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union,
    markedMemoryBefore, markedMemoryInternal, markedMemoryAfter, Finset.mem_filter, true_and]
  constructor
  · intro hj
    have hja : j ≠ A.min' hA := fun h => hj (h ▸ hamin)
    have hjc : j ≠ A.max' hA := fun h => hj (h ▸ hcmax)
    by_cases hl : j < A.min' hA
    · exact Or.inl (Or.inl hl)
    · by_cases hr : A.max' hA < j
      · exact Or.inr hr
      · exact Or.inl (Or.inr ⟨by omega, by omega, hj⟩)
  · rintro ((hl | hi) | hr) hj
    · have hh := A.min'_le j hj
      omega
    · exact hi.2.2 hj
    · have hh := A.le_max' j hj
      omega

theorem markedMemory_inactive_product {N : ℕ} (A : Finset (Fin (N+1))) (hA : A.Nonempty)
    (f : Fin (N+1) → ℝ) :
    (∏ j ∈ Finset.univ \ A, f j) =
      (∏ j ∈ markedMemoryBefore N (A.min' hA), f j) *
      (∏ j ∈ markedMemoryInternal A (A.min' hA) (A.max' hA), f j) *
      (∏ j ∈ markedMemoryAfter N (A.max' hA), f j) := by
  classical
  have hbi : Disjoint (markedMemoryBefore N (A.min' hA))
      (markedMemoryInternal A (A.min' hA) (A.max' hA)) := by
    apply Finset.disjoint_left.mpr
    intro j hj hi
    have hl := (Finset.mem_filter.mp hj).2
    have hr := (Finset.mem_filter.mp hi).2.1
    omega
  have hba : Disjoint (markedMemoryBefore N (A.min' hA)) (markedMemoryAfter N (A.max' hA)) := by
    apply Finset.disjoint_left.mpr
    intro j hj hi
    have hl := (Finset.mem_filter.mp hj).2
    have hr := (Finset.mem_filter.mp hi).2
    have hh := A.min'_le_max' hA
    omega
  have hia : Disjoint (markedMemoryInternal A (A.min' hA) (A.max' hA))
      (markedMemoryAfter N (A.max' hA)) := by
    apply Finset.disjoint_left.mpr
    intro j hj hi
    have hl := (Finset.mem_filter.mp hj).2.2.1
    have hr := (Finset.mem_filter.mp hi).2
    omega
  rw [markedMemory_inactive_partition A hA,
    Finset.prod_union (Finset.disjoint_union_left.mpr ⟨hba, hia⟩), Finset.prod_union hbi]

end ArtinMatthews
