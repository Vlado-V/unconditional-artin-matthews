module

public import ArtinMatthews.MarkedFiniteSpectralMoments
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Algebra.BigOperators.Fin


set_option backward.privateInPublic true
@[expose] public section

/-! Literal finite matrix words and their full state-path sums. -/
namespace ArtinMatthews
open Matrix
open scoped BigOperators Classical
noncomputable section

def markedMatrixWord {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : ℕ → Matrix ι ι ℂ) : ℕ → ℕ → Matrix ι ι ℂ
  | 0, _ => 1
  | n+1, j => K j*markedMatrixWord K n (j+1)

def markedMatrixPathWeight {ι : Type*} (K : ℕ → Matrix ι ι ℂ) :
    (n : ℕ) → ℕ → (Fin (n+1) → ι) → ℂ
  | 0, _, _ => 1
  | n+1, j, p => K j (p 0) (p 1)*markedMatrixPathWeight K n (j+1) (fun v => p v.succ)

theorem markedMatrixPathWeight_product {ι : Type*} (K : ℕ → Matrix ι ι ℂ)
    (n j : ℕ) (p : Fin (n+1) → ι) :
    markedMatrixPathWeight K n j p =
      ∏ v : Fin n, K (j+v.val) (p v.castSucc) (p v.succ) := by
  induction n generalizing j with
  | zero => simp [markedMatrixPathWeight]
  | succ n ih =>
    rw [Fin.prod_univ_succ]
    change K j (p 0) (p 1)*markedMatrixPathWeight K n (j+1) (fun v => p v.succ) = _
    rw [ih]
    congr 1
    apply Finset.prod_congr rfl
    intro v _
    rw [show (j+1)+v.val=j+(v.val+1) by omega]
    rfl

theorem markedMatrixWord_action_paths {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : ℕ → Matrix ι ι ℂ) (n j : ℕ) (g : ι → ℂ) (s : ι) :
    (markedMatrixWord K n j *ᵥ g) s =
      ∑ p : Fin n → ι, markedMatrixPathWeight K n j (Fin.cons (α := fun _ : Fin (n+1) => ι) s p)*
        g ((Fin.cons (α := fun _ : Fin (n+1) => ι) s p) (Fin.last n)) := by
  induction n generalizing j s with
  | zero => simp [markedMatrixWord,markedMatrixPathWeight]
  | succ n ih =>
    change ((K j*markedMatrixWord K n (j+1))*ᵥ g) s = _
    rw [← Matrix.mulVec_mulVec]
    change (∑ t, K j s t*(markedMatrixWord K n (j+1)*ᵥ g) t)=_
    simp_rw [ih,Finset.mul_sum]
    have he := Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n+1) => ι))
      (fun p => markedMatrixPathWeight K (n+1) j (Fin.cons (α := fun _ : Fin (n+2) => ι) s p)*
        g ((Fin.cons (α := fun _ : Fin (n+2) => ι) s p) (Fin.last (n+1))))
    rw [← he,Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro p _
    dsimp only [Fin.consEquiv,Equiv.coe_fn_mk]
    simp only [markedMatrixPathWeight,Fin.cons_zero,
      show (1:Fin (n+2))=(0:Fin (n+1)).succ by rfl,
      show Fin.last (n+1)=(Fin.last n).succ by rfl,Fin.cons_succ]
    ring

theorem markedMatrixWord_pairing_paths {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : ℕ → Matrix ι ι ℂ) (n j : ℕ) (f g : ι → ℂ) :
    markedMatrixPairing (markedMatrixWord K n j) f g =
      ∑ p : Fin (n+1) → ι, star (f (p 0))*markedMatrixPathWeight K n j p*g (p (Fin.last n)) := by
  change (∑ s, star (f s)*(markedMatrixWord K n j*ᵥ g) s)=_
  simp_rw [markedMatrixWord_action_paths,Finset.mul_sum]
  have he := Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n+1) => ι))
    (fun p => star (f (p 0))*markedMatrixPathWeight K n j p*g (p (Fin.last n)))
  rw [← he,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro p _
  dsimp only [Fin.consEquiv,Equiv.coe_fn_mk]
  simp only [Fin.cons_zero]
  ring

end
end ArtinMatthews
