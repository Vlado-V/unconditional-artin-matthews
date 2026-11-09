module

public import ArtinMatthews.GiantCandidatePrimeHits
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.GroupWithZero.Units.Fintype


set_option backward.privateInPublic true
@[expose] public section

/-! For a predecessor hit, the first coordinate is determined by the
remaining nonzero residues. Product hits are complementary to the
tuples of units. -/

namespace ArtinMatthews
noncomputable section
open Finset
open scoped BigOperators

private def giantCandidateProductOneEquiv (F : Type*) [Field F] (j : ℕ) :
    {t : Fin (j+1) → F // (∏ i,t i)=1} ≃ (Fin j → Fˣ) where
  toFun t i := Units.mk0 (t.val i.succ) (by
    have h : (∏ k,t.val k) ≠ 0 := by
      rw [t.property]
      exact one_ne_zero
    exact prod_ne_zero_iff.mp h i.succ (mem_univ i.succ))
  invFun u := ⟨Fin.cons (∏ i,(u i:F))⁻¹ (fun i => (u i:F)),by
    rw [Fin.prod_univ_succ]
    simp only [Fin.cons_zero,Fin.cons_succ]
    exact inv_mul_cancel₀ (prod_ne_zero_iff.mpr (fun i _ => (u i).ne_zero))⟩
  left_inv t := by
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun k => ?_) i
    · have h : t.val 0*(∏ k : Fin j,t.val k.succ)=1 := by
        simpa only [Fin.prod_univ_succ] using t.property
      have hden : (∏ k : Fin j,t.val k.succ) ≠ 0 := by
        intro he
        rw [he,mul_zero] at h
        exact zero_ne_one h
      change (∏ k : Fin j,t.val k.succ)⁻¹ = t.val 0
      rw [← one_div]
      exact ((eq_div_iff hden).mpr h).symm
    · rfl
  right_inv u := by
    funext i
    apply Units.ext
    rfl

private def giantCandidateProductNonzeroEquiv (F : Type*) [Field F] (j : ℕ) :
    {t : Fin j → F // (∏ i,t i)≠0} ≃ (Fin j → Fˣ) where
  toFun t i := Units.mk0 (t.val i) (prod_ne_zero_iff.mp t.property i (mem_univ i))
  invFun u := ⟨fun i => (u i:F),prod_ne_zero_iff.mpr (fun i _ => (u i).ne_zero)⟩
  left_inv t := by apply Subtype.ext; rfl
  right_inv u := by funext i; apply Units.ext; rfl

theorem giantCandidatePrimeHitMask_predecessor_card_succ (p j : ℕ) [Fact p.Prime] :
    (giantCandidatePrimeHitMask p (j+1) .predecessor).card = (p-1)^j := by
  classical
  rw [← Fintype.card_coe]
  let e : giantCandidatePrimeHitMask p (j+1) .predecessor ≃
      {t : Fin (j+1) → ZMod p // (∏ i,t i)=1} :=
    Equiv.subtypeEquivRight (fun t => mem_giantCandidatePrimeHitMask .predecessor t)
  rw [Fintype.card_congr (e.trans (giantCandidateProductOneEquiv (ZMod p) j)),
    Fintype.card_fun,Fintype.card_fin,Fintype.card_units,ZMod.card]

theorem giantCandidatePrimeHitMask_product_card (p j : ℕ) [Fact p.Prime] :
    (giantCandidatePrimeHitMask p j .product).card = p^j-(p-1)^j := by
  classical
  let S : Finset (Fin j → ZMod p) := univ
  let T := S.filter (fun t => (∏ i,t i)≠0)
  have hT : T.card=(p-1)^j := by
    rw [← Fintype.card_coe]
    let e : T ≃ {t : Fin j → ZMod p // (∏ i,t i)≠0} :=
      Equiv.subtypeEquivRight (fun t => by simp only [T,S,mem_filter,mem_univ,true_and])
    rw [Fintype.card_congr (e.trans (giantCandidateProductNonzeroEquiv (ZMod p) j)),
      Fintype.card_fun,Fintype.card_fin,Fintype.card_units,ZMod.card]
  have h := card_filter_add_card_filter_not (s:=S) (fun t => (∏ i,t i)=0)
  change (giantCandidatePrimeHitMask p j .product).card+T.card = S.card at h
  rw [hT,show S=univ from rfl,card_univ,Fintype.card_fun,Fintype.card_fin,ZMod.card] at h
  omega

end
end ArtinMatthews
