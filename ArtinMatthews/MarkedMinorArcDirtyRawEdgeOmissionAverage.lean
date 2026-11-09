module

public import ArtinMatthews.MarkedMinorArcDirtyPermutationAction
public import ArtinMatthews.MarkedMinorArcRawSlotAverage
public import ArtinMatthews.MarkedMinorArcRawGoodFirst


set_option backward.privateInPublic true
@[expose] public section

/-! The actual source slot symmetrization is exactly the uniform omission
expectation for every finite test, including all internal slot orders. -/
noncomputable section
namespace ArtinMatthews

open scoped BigOperators

def markedDirtySourceSlotWeight {J : Type*} [Fintype J] (n : ℕ)
    (_σ : J → Equiv.Perm (Fin (n+1))) : ℝ :=
  ∏ _j : J, 1/(Fintype.card (Equiv.Perm (Fin (n+1))):ℝ)

theorem markedDirtySourceSlotWeight_eq {J : Type*} [Fintype J] [DecidableEq J] (n : ℕ)
    (σ : J → Equiv.Perm (Fin (n+1))) :
    markedDirtySourceSlotWeight n σ = 1/(Fintype.card (J → Equiv.Perm (Fin (n+1))):ℝ) := by
  simp [markedDirtySourceSlotWeight,one_div]

theorem markedDirtySourceOmission_fiber_mass {J : Type*} [Fintype J] [DecidableEq J]
    (n : ℕ) (slot : Fin (n+1)) (o : J → Fin (n+1)) :
    (∑ σ : J → Equiv.Perm (Fin (n+1)),
      if (fun j => σ j slot)=o then markedDirtySourceSlotWeight n σ else 0)=
        markedUniformOmissionWeight (n+1) o := by
  classical
  have he (σ : J → Equiv.Perm (Fin (n+1))) :
      (if (fun j => σ j slot)=o then markedDirtySourceSlotWeight n σ else 0)=
        ∏ j, if σ j slot=o j then 1/(Fintype.card (Equiv.Perm (Fin (n+1))):ℝ) else 0 := by
    by_cases hall : ∀ j, σ j slot=o j
    · rw [ite_eq_left (funext hall)]
      unfold markedDirtySourceSlotWeight
      exact Finset.prod_congr rfl (fun j _ => (ite_eq_left (hall j)).symm)
    · rw [ite_eq_right (fun h => hall (congrFun h))]
      obtain ⟨j,hj⟩ := not_forall.mp hall
      exact (Finset.prod_eq_zero (Finset.mem_univ j) (ite_eq_right hj)).symm
  simp_rw [he]
  rw [← Fintype.prod_sum (fun j (σ : Equiv.Perm (Fin (n+1))) =>
    if σ slot=o j then 1/(Fintype.card (Equiv.Perm (Fin (n+1))):ℝ) else 0)]
  simp_rw [markedPermutation_slot_probability]
  simp only [markedUniformOmissionWeight,Nat.cast_add,Nat.cast_one]

theorem markedDirtySourceOmission_expectation {J : Type*} [Fintype J] [DecidableEq J]
    (n : ℕ) (slot : Fin (n+1)) (f : (J → Fin (n+1)) → ℝ) :
    (∑ σ : J → Equiv.Perm (Fin (n+1)), markedDirtySourceSlotWeight n σ*f (fun j => σ j slot))=
      ∑ o : J → Fin (n+1), markedUniformOmissionWeight (n+1) o*f o := by
  classical
  have he (σ : J → Equiv.Perm (Fin (n+1))) :
      markedDirtySourceSlotWeight n σ*f (fun j => σ j slot)=
        ∑ o : J → Fin (n+1),
          (if (fun j => σ j slot)=o then markedDirtySourceSlotWeight n σ else 0)*f o := by
    rw [Fintype.sum_eq_single (fun j => σ j slot)]
    · simp
    · intro o ho
      simp only [ite_eq_right ho.symm,zero_mul]
  calc
    _ = ∑ σ : J → Equiv.Perm (Fin (n+1)), ∑ o : J → Fin (n+1),
        (if (fun j => σ j slot)=o then markedDirtySourceSlotWeight n σ else 0)*f o :=
      Finset.sum_congr rfl (fun σ _ => he σ)
    _ = ∑ o : J → Fin (n+1), (∑ σ : J → Equiv.Perm (Fin (n+1)),
        if (fun j => σ j slot)=o then markedDirtySourceSlotWeight n σ else 0)*f o := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun _ _ => (Finset.sum_mul _ _ _).symm)
    _ = _ := by simp_rw [markedDirtySourceOmission_fiber_mass]

/-- This is the literal copied-prefix product under the actual state slot
permutation, before any physical or analytic test is imposed. -/
theorem markedDirtyRawStateSlot_copied_product {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (σ : J → Equiv.Perm (Fin (pads+1))) (s : MarkedRawState P (pads+1) B Z) :
    markedRawCopiedProduct ((markedRawActiveSplit pads) (markedRawSlotEquiv σ s).2.1).1=
      markedSourceCopiedProduct (markedRawNumericActive s.2.1) (fun j => σ j (Fin.last pads)) := by
  rw [markedRawCopiedProduct_eq_source]
  exact markedSourceCopiedProduct_permuted (markedRawNumericActive s.2.1) σ (fun _ => Fin.last pads)

end ArtinMatthews
