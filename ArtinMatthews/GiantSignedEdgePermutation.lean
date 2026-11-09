module

public import ArtinMatthews.GiantSignedEdgeIndices
public import ArtinMatthews.MarkedMinorArcRawMemoryGroupedJoint


set_option backward.privateInPublic true
@[expose] public section

/-! Ordered retrievals act on the final block of the canonical old tuple. -/

namespace ArtinMatthews
open scoped BigOperators
noncomputable section

def giantSignedAppendPermutation (n a : ℕ) (σ : Equiv.Perm (Fin a)) :
    Equiv.Perm (Fin (n + a)) :=
  (finSumFinEquiv.symm.trans (Equiv.sumCongr (Equiv.refl (Fin n)) σ)).trans finSumFinEquiv

theorem giantSignedAppendPermutation_left {n a : ℕ} (σ : Equiv.Perm (Fin a)) (i : Fin n) :
    giantSignedAppendPermutation n a σ (Fin.castAdd a i) = Fin.castAdd a i := by
  simp only [giantSignedAppendPermutation, Equiv.trans_apply, finSumFinEquiv_symm_apply_castAdd,
    Equiv.sumCongr_apply, Equiv.refl_apply, Sum.map_inl, finSumFinEquiv_apply_left]

theorem giantSignedAppendPermutation_right {n a : ℕ} (σ : Equiv.Perm (Fin a)) (i : Fin a) :
    giantSignedAppendPermutation n a σ (Fin.natAdd n i) = Fin.natAdd n (σ i) := by
  simp only [giantSignedAppendPermutation, Equiv.trans_apply, finSumFinEquiv_symm_apply_natAdd,
    Equiv.sumCongr_apply, Sum.map_inr, finSumFinEquiv_apply_right]

theorem giantSignedAppend_comp_permutation {X : Type*} {n a : ℕ}
    (u : Fin n → X) (p : Fin a → X) (σ : Equiv.Perm (Fin a)) :
    Fin.append u (p ∘ σ) = (Fin.append u p) ∘ giantSignedAppendPermutation n a σ := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp only [Fin.append_left, Function.comp_apply, giantSignedAppendPermutation_left]
  · intro j
    simp only [Fin.append_right, Function.comp_apply, giantSignedAppendPermutation_right]

def giantSignedGroupedTuplePermutation {J : Type*} {X : J → Type*} {a : J → ℕ}
    (σ : (j : J) → Equiv.Perm (Fin (a j))) :
    ((j : J) → Fin (a j) → X j) ≃ ((j : J) → Fin (a j) → X j) where
  toFun p j i := p j (σ j i)
  invFun p j i := p j ((σ j).symm i)
  left_inv p := by funext j i; simp
  right_inv p := by funext j i; simp

theorem giantSignedGroupedTuplePermutation_mass {J : Type*} [Fintype J]
    {X : J → Type*} {a : J → ℕ} (μ : (j : J) → X j → ℂ)
    (σ : (j : J) → Equiv.Perm (Fin (a j))) (p : (j : J) → Fin (a j) → X j) :
    (∏ j, ∏ i, μ j (giantSignedGroupedTuplePermutation σ p j i)) = ∏ j, ∏ i, μ j (p j i) := by
  classical
  apply Finset.prod_congr rfl
  intro j _
  exact Equiv.prod_comp (σ j) (fun i => μ j (p j i))

theorem giantSignedGroupedTupleSymmetric_append_right {J : Type*} {X : J → Type*}
    {n a : J → ℕ} (G : ((j : J) → Fin (n j + a j) → X j) → ℂ)
    (hG : MarkedRawGroupedTupleSymmetric (fun j => n j + a j) G)
    (u : (j : J) → Fin (n j) → X j) (p : (j : J) → Fin (a j) → X j)
    (σ : (j : J) → Equiv.Perm (Fin (a j))) :
    G (fun j => Fin.append (u j) (p j ∘ σ j)) = G (fun j => Fin.append (u j) (p j)) := by
  have he : (fun j => Fin.append (u j) (p j ∘ σ j)) =
      fun j => (Fin.append (u j) (p j)) ∘ giantSignedAppendPermutation (n j) (a j) (σ j) := by
    funext j
    exact giantSignedAppend_comp_permutation (u j) (p j) (σ j)
  rw [he]
  exact hG _ _

end
end ArtinMatthews
