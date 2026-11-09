module

public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Fin.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! Explicit finite-support coordinate equivalences for source summation. -/
namespace ArtinMatthews.SourceEuler
open scoped Classical
noncomputable section
variable {P X Y : Type} [Zero X] [Zero Y]

def finsuppPairEquiv : (P →₀ X × Y) ≃ ((P →₀ X) × (P →₀ Y)) where
  toFun a := (a.mapRange Prod.fst rfl, a.mapRange Prod.snd rfl)
  invFun a := Finsupp.onFinset (a.1.support ∪ a.2.support)
    (fun p => (a.1 p, a.2 p)) (by
      intro p hp
      by_contra hn
      have h1 : a.1 p = 0 := Finsupp.notMem_support_iff.mp
        (fun h => hn (Finset.mem_union_left _ h))
      have h2 : a.2 p = 0 := Finsupp.notMem_support_iff.mp
        (fun h => hn (Finset.mem_union_right _ h))
      exact hp (Prod.ext h1 h2))
  left_inv a := Finsupp.ext fun _ => rfl
  right_inv a := Prod.ext (Finsupp.ext fun _ => rfl) (Finsupp.ext fun _ => rfl)

theorem finsuppPairEquiv_apply_fst (a : P →₀ X × Y) (p : P) :
    (finsuppPairEquiv a).1 p = (a p).1 := rfl

theorem finsuppPairEquiv_apply_snd (a : P →₀ X × Y) (p : P) :
    (finsuppPairEquiv a).2 p = (a p).2 := rfl

theorem finsuppPairEquiv_symm_apply (a : (P →₀ X) × (P →₀ Y)) (p : P) :
    finsuppPairEquiv.symm a p = (a.1 p, a.2 p) := rfl

def finsuppFinTwoEquiv : (P →₀ Fin 2) ≃ {a : P →₀ ℕ // ∀ p, a p ≤ 1} where
  toFun a := ⟨a.mapRange Fin.val rfl, fun p => Nat.le_of_lt_succ (a p).isLt⟩
  invFun a := Finsupp.onFinset a.val.support
    (fun p => (⟨a.val p, Nat.lt_succ_of_le (a.property p)⟩ : Fin 2)) (by
      intro p hp
      by_contra hn
      apply hp
      apply Fin.ext
      exact Finsupp.notMem_support_iff.mp hn)
  left_inv a := Finsupp.ext fun _ => Fin.ext rfl
  right_inv a := Subtype.ext (Finsupp.ext fun _ => rfl)

theorem finsuppFinTwoEquiv_apply (a : P →₀ Fin 2) (p : P) :
    (finsuppFinTwoEquiv a).val p = (a p).val := rfl

theorem finsuppFinTwoEquiv_symm_apply (a : {a : P →₀ ℕ // ∀ p, a p ≤ 1}) (p : P) :
    (finsuppFinTwoEquiv.symm a p).val = a.val p := rfl

end
end ArtinMatthews.SourceEuler
