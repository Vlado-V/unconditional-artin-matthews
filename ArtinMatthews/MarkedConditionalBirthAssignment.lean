module

public import ArtinMatthews.MarkedOrderedPrimeReindex
public import Mathlib.Data.Fintype.Pi
public import ArtinMatthews.MarkedOrderedPrimeTupleMass
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

/-! A partial batch of performed births, with absent addresses retained
as none. Equalities to earlier addresses cost one actual prime atom for
every selected address, including dependencies inside the same batch. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def markedConditionalBirthValues {A : Type*}
    {P : A → Finset Nat.Primes} (old : A → Option Nat.Primes) (draw : Finset A)
    (t : (a : ↥draw) → ↥(P a.1)) (a : A) : Option Nat.Primes := by
  classical
  exact if ha : a∈draw then some (t ⟨a,ha⟩).1 else old a

def MarkedConditionalBirthGate {A : Type*}
    {P : A → Finset Nat.Primes} (S : Finset A) (parent : A → A)
    (old : A → Option Nat.Primes) (draw : Finset A) (t : (a : ↥draw) → ↥(P a.1)) : Prop :=
  ∀ a∈S, markedConditionalBirthValues old draw t a≠none ∧
    markedConditionalBirthValues old draw t a=markedConditionalBirthValues old draw t (parent a)

def markedConditionalBirthTarget {A : Type*} [LinearOrder A]
    (parent : A → A) (old : A → Option Nat.Primes) (draw : Finset A)
    (a : ↥draw) (prior : {b : ↥draw // b<a} → Nat.Primes) : Option Nat.Primes :=
  if h : parent a.1∈draw ∧ parent a.1<a.1 then
    some (prior ⟨⟨parent a.1,h.1⟩,h.2⟩)
  else old (parent a.1)

set_option backward.isDefEq.respectTransparency false in
theorem markedConditionalBirth_sum_le {A : Type*} [LinearOrder A] [Fintype A]
    {P : A → Finset Nat.Primes} (ν : (a : A) → ↥(P a) → ℝ)
    (hν : ∀ a p,0 ≤ ν a p) {Δ N : ℝ} (hΔ : 0 ≤ Δ) (hN : 1 ≤ N)
    (hatom : ∀ a p,ν a p ≤ Δ) (hmass : ∀ a,(∑ p : P a,ν a p) ≤ N)
    (S : Finset A) (parent : A → A) (old : A → Option Nat.Primes) (draw : Finset A)
    (hearlier : ∀ a∈S,parent a<a) (habsent : ∀ a∈S,a∉draw → old a=none) :
    (∑ t : (a : ↥draw) → ↥(P a.1),
      if MarkedConditionalBirthGate S parent old draw t then ∏ a,ν a.1 (t a) else 0) ≤
      Δ^S.card*N^draw.card := by
  by_cases hsub : S ⊆ draw
  · let SD : Finset ↥draw := Finset.univ.filter (fun a => a.1∈S)
    have hcard : SD.card=S.card := by
      let E : ↥SD ≃ ↥S :=
        { toFun := fun a => ⟨a.1.1,(Finset.mem_filter.mp a.2).2⟩
          invFun := fun a => ⟨⟨a.1,hsub a.2⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,a.2⟩⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      simpa only [Fintype.card_coe] using Fintype.card_congr E
    have himp (t : (a : ↥draw) → ↥(P a.1))
        (ht : MarkedConditionalBirthGate S parent old draw t) :
        MarkedOrderedPrimeTuplePrescribed SD (markedConditionalBirthTarget parent old draw) t := by
      intro a ha
      have haS : a.1∈S := (Finset.mem_filter.mp ha).2
      have hpLt : parent a.1<a.1 := hearlier a.1 haS
      have he := (ht a.1 haS).2
      have hva : markedConditionalBirthValues old draw t a.1=some (t a).1 := by
        simp only [markedConditionalBirthValues,dite_eq_left a.2]
      rw [hva] at he
      by_cases hp : parent a.1∈draw
      · unfold markedConditionalBirthTarget
        rw [dite_eq_left ⟨hp,hpLt⟩]
        simpa only [markedConditionalBirthValues,dite_eq_left hp,markedOrderedPrimeTuplePrefix] using he
      · unfold markedConditionalBirthTarget
        rw [dite_eq_right (fun h => hp h.1)]
        simpa only [markedConditionalBirthValues,dite_eq_right hp] using he
    have hs : (∑ t : (a : ↥draw) → ↥(P a.1),
        if MarkedConditionalBirthGate S parent old draw t then ∏ a,ν a.1 (t a) else 0) ≤
        ∑ t : (a : ↥draw) → ↥(P a.1),
          if MarkedOrderedPrimeTuplePrescribed SD (markedConditionalBirthTarget parent old draw) t
          then ∏ a,ν a.1 (t a) else 0 := by
      apply Finset.sum_le_sum
      intro t _
      by_cases ht : MarkedConditionalBirthGate S parent old draw t
      · rw [ite_eq_left ht,ite_eq_left (himp t ht)]
      · rw [ite_eq_right ht]
        split_ifs
        · exact Finset.prod_nonneg (fun a _ => hν a.1 _)
        · exact le_rfl
    have hbound := markedOrderedPrimeTuple_sum_le_slack (fun a : ↥draw => ν a.1)
      (fun a => hν a.1) hΔ hN (fun a => hatom a.1) (fun a => hmass a.1)
      SD (markedConditionalBirthTarget parent old draw)
    rw [hcard,Fintype.card_coe] at hbound
    apply hs.trans
    refine le_trans (le_of_eq ?_) hbound
    apply Finset.sum_congr (by ext; simp only [Finset.mem_univ])
    intro t _
    rfl
  · obtain ⟨a,ha,had⟩ := Finset.not_subset.mp hsub
    have hz : (∑ t : (a : ↥draw) → ↥(P a.1),
        if MarkedConditionalBirthGate S parent old draw t then ∏ a,ν a.1 (t a) else 0)=0 := by
      apply Finset.sum_eq_zero
      intro t _
      apply ite_eq_right
      intro ht
      exact (ht a ha).1 (by simp only [markedConditionalBirthValues,dite_eq_right had,habsent a ha had])
    rw [hz]
    exact mul_nonneg (pow_nonneg hΔ _) (pow_nonneg (zero_le_one.trans hN) _)

end ArtinMatthews
