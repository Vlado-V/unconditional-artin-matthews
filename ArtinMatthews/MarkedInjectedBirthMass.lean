module

public import ArtinMatthews.MarkedConditionalBirthAssignment
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
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
public import Mathlib.Topology.Sheaves.Init


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
