module

public import ArtinMatthews.MarkedConditionalBirthAssignment


set_option backward.privateInPublic true
@[expose] public section

/-! Reindex actual performed draw coordinates into their potential
addresses. The map is injective, so both tuple multiplicities and every
atom factor are preserved. Absent potential addresses remain explicit. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def markedBirthDrawSet {A I : Type*} [Fintype I] (e : I → A) : Finset A := by
  classical
  exact Finset.univ.image e

def markedBirthDrawEquiv {A I : Type*} [Fintype I]
    (e : I → A) (he : Function.Injective e) : I ≃ ↥(markedBirthDrawSet e) := by
  classical
  exact Equiv.ofBijective (fun i => ⟨e i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩)
    ⟨fun _ _ h => he (congrArg Subtype.val h),by
      intro a
      obtain ⟨i,_,hi⟩ := Finset.mem_image.mp a.2
      exact ⟨i,Subtype.ext hi⟩⟩

def markedBirthDrawTupleEquiv {A I : Type*} [Fintype I]
    (P : A → Finset Nat.Primes) (e : I → A) (he : Function.Injective e) :
    ((i : I) → ↥(P (e i))) ≃ ((a : ↥(markedBirthDrawSet e)) → ↥(P a.1)) :=
  Equiv.piCongrLeft (fun a : ↥(markedBirthDrawSet e) => ↥(P a.1)) (markedBirthDrawEquiv e he)

theorem markedBirthDrawTupleEquiv_apply {A I : Type*} [Fintype I]
    (P : A → Finset Nat.Primes) (e : I → A) (he : Function.Injective e)
    (t : (i : I) → ↥(P (e i))) (i : I) :
    markedBirthDrawTupleEquiv P e he t (markedBirthDrawEquiv e he i)=t i :=
  Equiv.piCongrLeft_apply_apply _ _ _ _

theorem markedBirthDrawTuple_product {A I : Type*} [Fintype I]
    (P : A → Finset Nat.Primes) (e : I → A) (he : Function.Injective e)
    (ν : (a : A) → ↥(P a) → ℝ) (t : (i : I) → ↥(P (e i))) :
    (∏ a : ↥(markedBirthDrawSet e),ν a.1 (markedBirthDrawTupleEquiv P e he t a))=
      ∏ i,ν (e i) (t i) := by
  rw [← (markedBirthDrawEquiv e he).prod_comp]
  apply Finset.prod_congr rfl
  intro i _
  rw [markedBirthDrawTupleEquiv_apply]
  rfl

theorem markedBirthDrawValues_apply {A I : Type*} [Fintype I]
    (P : A → Finset Nat.Primes) (e : I → A) (he : Function.Injective e)
    (old : A → Option Nat.Primes) (t : (i : I) → ↥(P (e i))) (i : I) :
    markedConditionalBirthValues old (markedBirthDrawSet e)
      (markedBirthDrawTupleEquiv P e he t) (e i)=some (t i).1 := by
  classical
  have hi : e i∈markedBirthDrawSet e := Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  rw [markedConditionalBirthValues,dite_eq_left hi]
  exact congrArg (fun p => some p.1) (markedBirthDrawTupleEquiv_apply P e he t i)

theorem markedInjectedBirth_sum_le
    {A I : Type*} [LinearOrder A] [Fintype A] [Fintype I]
    {P : A → Finset Nat.Primes} (ν : (a : A) → ↥(P a) → ℝ)
    (hν : ∀ a p,0 ≤ ν a p) {Δ N : ℝ} (hΔ : 0 ≤ Δ) (hN : 1 ≤ N)
    (hatom : ∀ a p,ν a p ≤ Δ) (hmass : ∀ a,(∑ p : P a,ν a p) ≤ N)
    (e : I → A) (he : Function.Injective e)
    (S : Finset A) (parent : A → A) (old : A → Option Nat.Primes)
    (hearlier : ∀ a∈S,parent a<a)
    (habsent : ∀ a∈S,a∉markedBirthDrawSet e → old a=none) :
    (∑ t : (i : I) → ↥(P (e i)),
      if MarkedConditionalBirthGate S parent old (markedBirthDrawSet e)
          (markedBirthDrawTupleEquiv P e he t) then ∏ i,ν (e i) (t i) else 0) ≤
      Δ^S.card*N^(Fintype.card I) := by
  have h := markedConditionalBirth_sum_le ν hν hΔ hN hatom hmass S parent old
    (markedBirthDrawSet e) hearlier habsent
  have heq := (markedBirthDrawTupleEquiv P e he).sum_comp
    (fun t => if MarkedConditionalBirthGate S parent old (markedBirthDrawSet e) t then
      ∏ a : ↥(markedBirthDrawSet e),ν a.1 (t a) else 0)
  simp_rw [markedBirthDrawTuple_product] at heq
  rw [← heq] at h
  have hc : (markedBirthDrawSet e).card=Fintype.card I := by
    simpa only [Fintype.card_coe] using (Fintype.card_congr (markedBirthDrawEquiv e he)).symm
  simpa only [hc] using h

end ArtinMatthews
