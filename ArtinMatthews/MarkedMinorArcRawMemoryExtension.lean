module

public import ArtinMatthews.MarkedMinorArcRawMemoryAmbient


set_option backward.privateInPublic true
@[expose] public section

/-! Exact total-cutoff zero extension and the literal symmetric-pending
condition inside the actual independent-group Fock coordinates. -/
namespace ArtinMatthews
open scoped BigOperators

/-- Zero extension from the true total-truncated pending memory to the
literal independent-group ambient coordinates. -/
noncomputable def markedRawMemoryExtend {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {B : ℕ} (f : MarkedRawMemory P B → ℂ)
    (m : MarkedRawAmbientMemory P B) : ℂ := by
  classical
  exact if h : markedRawAmbientMemoryTotal m ≤ B then
    f ((markedRawMemoryAmbientEquiv P B).symm ⟨m,h⟩) else 0

theorem markedRawAmbientMemoryTotal_permute {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {B : ℕ} (m : MarkedRawAmbientMemory P B)
    (σ : (j : J) → Equiv.Perm (Fin ((m j).1 : ℕ))) :
    markedRawAmbientMemoryTotal (markedRawAmbientMemoryPermute m σ)=markedRawAmbientMemoryTotal m := rfl

/-- The inverse tensor identification commutes with every literal old-index
permutation, including all source size and total-cutoff proofs. -/
theorem markedRawAmbientToMemory_permute {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {B : ℕ} (m : MarkedRawAmbientMemory P B)
    (hm : markedRawAmbientMemoryTotal m ≤ B)
    (σ : (j : J) → Equiv.Perm (Fin ((m j).1 : ℕ))) :
    (markedRawMemoryAmbientEquiv P B).symm
      ⟨markedRawAmbientMemoryPermute m σ,hm⟩=
      markedRawMemoryPermute ((markedRawMemoryAmbientEquiv P B).symm ⟨m,hm⟩) σ := rfl

/-- Symmetric actual memory functions extend to symmetric ambient functions,
with the actual total cutoff retained. -/
theorem markedRawMemoryExtend_permute {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {B : ℕ} (f : MarkedRawMemory P B → ℂ)
    (hf : MarkedRawMemorySymmetric f) (m : MarkedRawAmbientMemory P B)
    (σ : (j : J) → Equiv.Perm (Fin ((m j).1 : ℕ))) :
    markedRawMemoryExtend f (markedRawAmbientMemoryPermute m σ)=markedRawMemoryExtend f m := by
  classical
  change (if hm : markedRawAmbientMemoryTotal m ≤ B then
      f ((markedRawMemoryAmbientEquiv P B).symm ⟨markedRawAmbientMemoryPermute m σ,hm⟩) else 0)=
    (if hm : markedRawAmbientMemoryTotal m ≤ B then
      f ((markedRawMemoryAmbientEquiv P B).symm ⟨m,hm⟩) else 0)
  split_ifs with hm
  · exact hf ((markedRawMemoryAmbientEquiv P B).symm ⟨m,hm⟩) σ
  · rfl

/-- Zero extension agrees with the original actual function on every true
memory state; no choice of particle representatives is made. -/
theorem markedRawMemoryExtend_apply {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {B : ℕ} (f : MarkedRawMemory P B → ℂ)
    (m : MarkedRawMemory P B) : markedRawMemoryExtend f (markedRawMemoryToAmbient m)=f m := by
  classical
  unfold markedRawMemoryExtend
  have hm : markedRawAmbientMemoryTotal (markedRawMemoryToAmbient m) ≤ B :=
    (markedRawMemoryAmbientEquiv P B m).2
  rw [dite_eq_left hm]
  change f ((markedRawMemoryAmbientEquiv P B).symm (markedRawMemoryAmbientEquiv P B m))=_
  rw [Equiv.symm_apply_apply]

/-- Literal total-cutoff zero extension preserves the true factorial
weighted energy, including zero or repeated prime/anchor atoms. -/
theorem markedRawMemoryExtend_energy {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ)
    (B : ℕ) (f : MarkedRawMemory P B → ℂ) :
    (∑ m : MarkedRawAmbientMemory P B, markedRawAmbientMemoryMass ν m*‖markedRawMemoryExtend f m‖^2)=
      ∑ m : MarkedRawMemory P B, markedRawMemoryMass ν m*‖f m‖^2 := by
  classical
  rw [markedRawMemory_energy_ambient ν B f]
  symm
  let g : MarkedRawAmbientMemory P B → ℝ := fun m =>
    markedRawAmbientMemoryMass ν m*‖markedRawMemoryExtend f m‖^2
  calc
    _ = ∑ m : {m : MarkedRawAmbientMemory P B // markedRawAmbientMemoryTotal m ≤ B}, g m.1 := by
      apply Finset.sum_congr rfl
      intro m _
      dsimp only [g]
      simp only [markedRawMemoryExtend,dite_eq_left m.2]
    _ = ∑ m ∈ (Finset.univ : Finset (MarkedRawAmbientMemory P B)).filter
        (fun m => markedRawAmbientMemoryTotal m ≤ B), g m :=
      (Finset.sum_subtype _ (by simp) g).symm
    _ = _ := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro m _ hm
      have hn : ¬markedRawAmbientMemoryTotal m ≤ B := by
        simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using hm
      dsimp only [g,markedRawMemoryExtend]
      rw [dite_eq_right hn]
      simp only [norm_zero,zero_pow (by decide : 2≠0),mul_zero]

end ArtinMatthews
