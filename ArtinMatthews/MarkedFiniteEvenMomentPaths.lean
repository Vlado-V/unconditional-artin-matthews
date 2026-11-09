module

public import ArtinMatthews.MarkedFiniteMatrixPaths


set_option backward.privateInPublic true
@[expose] public section

/-! Even AA* moments as alternating full-state paths. The boundary
condition identifies positions only, and never identifies endpoint lists. -/
namespace ArtinMatthews
open Matrix
open scoped BigOperators Classical ComplexOrder
noncomputable section

def markedAlternatingMatrix {ι : Type*} (A : Matrix ι ι ℂ) (j : ℕ) : Matrix ι ι ℂ :=
  if j%2=0 then A else Aᴴ

theorem markedAlternatingMatrix_period_two {ι : Type*} (A : Matrix ι ι ℂ) (j : ℕ) :
    markedAlternatingMatrix A (j+2)=markedAlternatingMatrix A j := by
  simp only [markedAlternatingMatrix,Nat.add_mod,Nat.mod_self,add_zero,Nat.mod_mod]

theorem markedMatrixWord_period_two {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : ℕ → Matrix ι ι ℂ) (hK : ∀ j,K (j+2)=K j) (n j : ℕ) :
    markedMatrixWord K n (j+2)=markedMatrixWord K n j := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
    simp only [markedMatrixWord,hK]
    rw [show (j+2)+1=(j+1)+2 by omega,ih]

theorem markedMatrixWord_alternating_even {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (R : ℕ) :
    markedMatrixWord (markedAlternatingMatrix A) (2*R) 0=(A*Aᴴ)^R := by
  induction R with
  | zero => simp only [markedMatrixWord,pow_zero]
  | succ R ih =>
    rw [show 2*(R+1)=(2*R+1)+1 by omega,markedMatrixWord,markedMatrixWord]
    change A*(Aᴴ*markedMatrixWord (markedAlternatingMatrix A) (2*R) 2)=(A*Aᴴ)^(R+1)
    rw [show (2:ℕ)=0+2 by rfl,
      markedMatrixWord_period_two _ (markedAlternatingMatrix_period_two A),ih,pow_succ']
    exact (Matrix.mul_assoc _ _ _).symm

theorem markedEvenMoment_indicator_paths {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι ι ℂ) (pos : ι → κ) (x : κ) (R : ℕ) :
    markedQuadraticForm ((A*Aᴴ)^R) (fun s => if pos s=x then 1 else 0) =
      (∑ p : Fin (2*R+1) → ι, if pos (p 0)=x ∧ pos (p (Fin.last (2*R)))=x then
        markedMatrixPathWeight (markedAlternatingMatrix A) (2*R) 0 p else 0).re := by
  have h := markedMatrixWord_pairing_paths (markedAlternatingMatrix A) (2*R) 0
    (fun s => if pos s=x then 1 else 0) (fun s => if pos s=x then 1 else 0)
  rw [markedMatrixWord_alternating_even] at h
  change (markedMatrixPairing ((A*Aᴴ)^R) _ _).re=_
  rw [h]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  by_cases hs : pos (p 0)=x <;> by_cases ht : pos (p (Fin.last (2*R)))=x <;>
    simp [hs,ht]

theorem markedPosition_boundary_sum {κ : Type*} [Fintype κ] [DecidableEq κ]
    (x y : κ) (z : ℂ) :
    (∑ a, if x=a ∧ y=a then z else 0)=if x=y then z else 0 := by
  rw [Finset.sum_eq_single x]
  · by_cases h : x=y <;> simp [h,eq_comm]
  · intro a _ ha
    have hn : x≠a := Ne.symm ha
    simp only [hn,false_and,ite_false]
  · simp

theorem markedEvenMoment_position_trace_paths {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι ℂ) (pos : ι → κ) (R : ℕ) :
    (∑ x, markedQuadraticForm ((A*Aᴴ)^R) (fun s => if pos s=x then 1 else 0)) =
      (∑ p : Fin (2*R+1) → ι,
        if pos (p 0)=pos (p (Fin.last (2*R))) then
          markedMatrixPathWeight (markedAlternatingMatrix A) (2*R) 0 p else 0).re := by
  simp_rw [markedEvenMoment_indicator_paths]
  rw [← markedComplex_re_sum,Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  exact markedPosition_boundary_sum _ _ _

end
end ArtinMatthews
