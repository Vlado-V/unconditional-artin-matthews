module

public import ArtinMatthews.IdealProbeFraction
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

/-! The Hoeffding supports surviving all designated probes and all
omitted tail coordinates are counted exactly. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def idealProbeSupports {ι : Type*} [DecidableEq ι] (U P T : Finset ι) (j : ℕ) : Finset (Finset ι) :=
  (U.powersetCard j).filter (fun S => P ⊆ S ∧ Disjoint S T)

theorem mem_idealProbeSupports {ι : Type*} [DecidableEq ι] {U P T S : Finset ι} {j : ℕ} :
    S ∈ idealProbeSupports U P T j ↔ S ⊆ U ∧ S.card=j ∧ P ⊆ S ∧ Disjoint S T := by
  simp only [idealProbeSupports, mem_filter, mem_powersetCard, and_assoc]

theorem idealProbeSupports_card {ι : Type*} [DecidableEq ι]
    {U P T : Finset ι} (hP : P ⊆ U) (hT : T ⊆ U) (hPT : Disjoint P T)
    {j : ℕ} (hj : P.card ≤ j) :
    (idealProbeSupports U P T j).card=(U.card-P.card-T.card).choose (j-P.card) := by
  let W := U \ (P ∪ T)
  have hPU : P ∪ T ⊆ U := union_subset hP hT
  have hW : W.card=U.card-P.card-T.card := by
    rw [card_sdiff_of_subset hPU, card_union_of_disjoint hPT, Nat.sub_add_eq]
  have hc : (idealProbeSupports U P T j).card=(W.powersetCard (j-P.card)).card := by
    apply card_nbij' (fun S => S \ P) (fun A => P ∪ A)
    · intro S hS
      obtain ⟨hSU,hSj,hPS,hST⟩ := mem_idealProbeSupports.mp hS
      apply mem_powersetCard.mpr
      constructor
      · intro x hx
        obtain ⟨hxS,hxP⟩ := mem_sdiff.mp hx
        apply mem_sdiff.mpr
        refine ⟨hSU hxS,?_⟩
        intro hx
        rcases mem_union.mp hx with hp | ht
        · exact hxP hp
        · exact disjoint_left.mp hST hxS ht
      · rw [card_sdiff_of_subset hPS,hSj]
    · intro A hA
      obtain ⟨hAW,hAj⟩ := mem_powersetCard.mp hA
      have hPA : Disjoint P A := by
        apply disjoint_left.mpr
        intro x hxP hxA
        exact (mem_sdiff.mp (hAW hxA)).2 (mem_union_left T hxP)
      apply mem_idealProbeSupports.mpr
      refine ⟨?_,?_,subset_union_left,?_⟩
      · exact union_subset hP (fun x hx => (mem_sdiff.mp (hAW hx)).1)
      · rw [card_union_of_disjoint hPA,hAj,Nat.add_sub_cancel' hj]
      · apply disjoint_left.mpr
        intro x hx hxT
        rcases mem_union.mp hx with hxP | hxA
        · exact disjoint_left.mp hPT hxP hxT
        · exact (mem_sdiff.mp (hAW hxA)).2 (mem_union_right P hxT)
    · intro S hS
      have hPS := (mem_idealProbeSupports.mp hS).2.2.1
      ext x
      simp only [mem_union,mem_sdiff]
      constructor
      · rintro (hp | ⟨hx,_⟩)
        · exact hPS hp
        · exact hx
      · intro hx
        by_cases hp : x∈P
        · exact Or.inl hp
        · exact Or.inr ⟨hx,hp⟩
    · intro A hA
      have hAW := (mem_powersetCard.mp hA).1
      ext x
      simp only [mem_union,mem_sdiff]
      constructor
      · rintro ⟨hp | ha,hnp⟩
        · exact (hnp hp).elim
        · exact ha
      · intro hx
        exact ⟨Or.inr hx,fun hp => (mem_sdiff.mp (hAW hx)).2 (mem_union_left T hp)⟩
  rw [hc,card_powersetCard,hW]

theorem idealProbeSupports_card_zero {ι : Type*} [DecidableEq ι]
    {U P T : Finset ι} (hT : T ⊆ U) {j : ℕ}
    (h : ¬(P.card ≤ j ∧ j+T.card ≤ U.card)) :
    (idealProbeSupports U P T j).card=0 := by
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro S hS
  obtain ⟨hSU,hSj,hPS,hST⟩ := mem_idealProbeSupports.mp hS
  apply h
  refine ⟨hSj ▸ card_le_card hPS,?_⟩
  have hu := card_le_card (union_subset hSU hT)
  rw [card_union_of_disjoint hST,hSj] at hu
  exact hu

theorem idealProbeSupports_fraction {ι : Type*} [DecidableEq ι]
    {U P T : Finset ι} (hP : P ⊆ U) (hT : T ⊆ U) (hPT : Disjoint P T) (j : ℕ) :
    ((idealProbeSupports U P T j).card : ℝ)/(U.card.choose j)=
      idealProbeSurvivorFraction U.card P.card T.card j := by
  by_cases h : P.card ≤ j ∧ j+T.card ≤ U.card
  · rw [idealProbeSupports_card hP hT hPT h.1,idealProbeSurvivorFraction,ite_eq_left h]
  · rw [idealProbeSupports_card_zero hT h,idealProbeSurvivorFraction,ite_eq_right h]
    simp

theorem idealProbeSupports_uniform_weight {ι : Type*} [DecidableEq ι]
    {U P T : Finset ι} (hP : P ⊆ U) (hT : T ⊆ U) (hPT : Disjoint P T)
    (hU : 0 < U.card) (hm : 1 ≤ P.card) (hell : 1 ≤ T.card)
    (hlarge : (P.card+T.card)*(P.card+T.card-1) ≤ U.card)
    (j : ℕ) (w : Finset ι → ℝ) (hw : ∀ S∈U.powersetCard j,0 ≤ w S)
    (hsym : ∀ S∈U.powersetCard j,∀ S'∈U.powersetCard j,w S=w S') :
    (∑ S∈idealProbeSupports U P T j,w S) ≤
      (2/(P.card+1 : ℕ)) * ∑ S∈U.powersetCard j,w S := by
  by_cases hj : j ≤ U.card
  · have hnonempty : (U.powersetCard j).Nonempty := by
      apply card_pos.mp
      rw [card_powersetCard]
      exact Nat.choose_pos hj
    obtain ⟨S₀,hS₀⟩ := hnonempty
    have hconst : (∑ S∈U.powersetCard j,w S)=((U.card.choose j : ℕ):ℝ)*w S₀ := by
      calc
        _ = ∑ _S∈U.powersetCard j,w S₀ := sum_congr rfl (fun S hS => hsym S hS S₀ hS₀)
        _ = _ := by rw [sum_const,nsmul_eq_mul,card_powersetCard]
    have hchosen : (∑ S∈idealProbeSupports U P T j,w S)=
        ((idealProbeSupports U P T j).card:ℝ)*w S₀ := by
      calc
        _ = ∑ _S∈idealProbeSupports U P T j,w S₀ := by
          apply sum_congr rfl
          intro S hS
          exact hsym S (mem_filter.mp hS).1 S₀ hS₀
        _ = _ := by rw [sum_const,nsmul_eq_mul]
    rw [hconst,hchosen]
    have hcard := (idealProbeSupports_fraction hP hT hPT j).trans_le
      (idealProbeSurvivorFraction_le hU hm hell hlarge)
    have hcard' := (div_le_iff₀ (Nat.cast_pos.mpr (Nat.choose_pos hj))).mp hcard
    exact (mul_le_mul_of_nonneg_right hcard' (hw S₀ hS₀)).trans_eq (mul_assoc _ _ _)
  · have he : U.powersetCard j=∅ := card_eq_zero.mp (by rw [card_powersetCard,Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hj)])
    simp [idealProbeSupports,he]

end
end ArtinMatthews
