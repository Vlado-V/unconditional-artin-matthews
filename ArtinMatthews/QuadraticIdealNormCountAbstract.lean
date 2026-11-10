module

public import Mathlib.SetTheory.Cardinal.Finite
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
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! A sharp two-prime multiset fiber count for quadratic ideal norms. -/

noncomputable section
namespace ArtinMatthews

open scoped BigOperators

private theorem multiset_norm_product_pair {M : Type*} [DecidableEq M]
    (N : M → ℕ) (P Q : M) (hPQ : P ≠ Q) (s : Multiset M) :
    (∀ x ∈ s, x = P ∨ x = Q) →
      (s.map N).prod = N P ^ s.count P * N Q ^ s.count Q := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons x s ih =>
    intro hs
    have hss : ∀ y ∈ s, y = P ∨ y = Q := fun y hy => hs y (Multiset.mem_cons_of_mem hy)
    have hh := ih hss
    rcases hs x (by simp) with rfl | rfl
    · simp [Ne.symm hPQ, hh, pow_succ, mul_comm, mul_left_comm]
    · simp [hPQ, hh, pow_succ, mul_comm, mul_left_comm]

private theorem multiset_eq_of_single_count {M : Type*} [DecidableEq M]
    (P : M) (s t : Multiset M)
    (hs : ∀ x ∈ s, x = P) (ht : ∀ x ∈ t, x = P)
    (hcount : s.count P = t.count P) : s = t := by
  ext x
  by_cases hx : x = P
  · simpa only [hx] using hcount
  · have hxs : x ∉ s := fun h => hx (hs x h)
    have hxt : x ∉ t := fun h => hx (ht x h)
    simp only [Multiset.count_eq_zero.mpr hxs, Multiset.count_eq_zero.mpr hxt]

private theorem multiset_eq_of_pair_norm_count {M : Type*} [DecidableEq M]
    (N : M → ℕ) (P Q : M) (hPQ : P ≠ Q) (hNP : 2 ≤ N P) (hNQ : 2 ≤ N Q)
    (s t : Multiset M)
    (hs : ∀ x ∈ s, x = P ∨ x = Q) (ht : ∀ x ∈ t, x = P ∨ x = Q)
    (hprod : (s.map N).prod = (t.map N).prod)
    (hcount : s.count P = t.count P) : s = t := by
  rw [multiset_norm_product_pair N P Q hPQ s hs,
    multiset_norm_product_pair N P Q hPQ t ht, hcount] at hprod
  have hpow : N Q ^ s.count Q = N Q ^ t.count Q :=
    Nat.eq_of_mul_eq_mul_left (pow_pos (by omega : 0 < N P) _) hprod
  have hcountQ : s.count Q = t.count Q := Nat.pow_right_injective hNQ hpow
  ext x
  by_cases hxP : x = P
  · simpa only [hxP] using hcount
  by_cases hxQ : x = Q
  · simpa only [hxQ] using hcountQ
  have hxs : x ∉ s := by intro h; exact (hs x h).elim hxP hxQ
  have hxt : x ∉ t := by intro h; exact (ht x h).elim hxP hxQ
  simp only [Multiset.count_eq_zero.mpr hxs, Multiset.count_eq_zero.mpr hxt]

private theorem card_le_of_count_injective {A M : Type*} [DecidableEq M]
    (f : A → Multiset M) (P : M) (r : ℕ)
    (hlen : ∀ a, (f a).card ≤ r)
    (hinj : Function.Injective (fun a => (f a).count P)) : Nat.card A ≤ r + 1 := by
  let g : A → Fin (r + 1) := fun a =>
    ⟨(f a).count P, Nat.lt_succ_of_le ((Multiset.count_le_card P (f a)).trans (hlen a))⟩
  have hg : Function.Injective g := by
    intro a b h
    exact hinj (congrArg Fin.val h)
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective g hg

/-- With at most two available primes and fixed product norm, counting one
prime exponent determines every multiset. The sharp fiber bound is `r+1`,
including unequal residue degrees. -/
theorem two_support_multiset_norm_fiber_card_le {A M : Type*} [DecidableEq M] [Nonempty M]
    (f : A → Multiset M) (hf : Function.Injective f) (S : Finset M)
    (hS : S.card ≤ 2) (hs : ∀ a x, x ∈ f a → x ∈ S)
    (N : M → ℕ) (hN : ∀ P ∈ S, 2 ≤ N P)
    (L r : ℕ) (hprod : ∀ a, ((f a).map N).prod = L)
    (hlen : ∀ a, (f a).card ≤ r) : Nat.card A ≤ r + 1 := by
  classical
  by_cases h0 : S = ∅
  · apply card_le_of_count_injective f (Classical.arbitrary M) r hlen
    intro a b _
    apply hf
    ext x
    have hxs : x ∉ f a := by intro h; simpa only [h0, Finset.notMem_empty] using hs a x h
    have hxt : x ∉ f b := by intro h; simpa only [h0, Finset.notMem_empty] using hs b x h
    simp only [Multiset.count_eq_zero.mpr hxs, Multiset.count_eq_zero.mpr hxt]
  by_cases h1 : S.card = 1
  · obtain ⟨P, hP⟩ := Finset.card_eq_one.mp h1
    apply card_le_of_count_injective f P r hlen
    intro a b hc
    apply hf
    apply multiset_eq_of_single_count P (f a) (f b) _ _ hc
    · intro x hx
      simpa only [hP, Finset.mem_singleton] using hs a x hx
    · intro x hx
      simpa only [hP, Finset.mem_singleton] using hs b x hx
  have h2 : S.card = 2 := by
    have hpos : 0 < S.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr h0)
    omega
  obtain ⟨P, Q, hPQ, hS'⟩ := Finset.card_eq_two.mp h2
  apply card_le_of_count_injective f P r hlen
  intro a b hc
  apply hf
  apply multiset_eq_of_pair_norm_count N P Q hPQ
    (hN P (by simp [hS'])) (hN Q (by simp [hS'])) (f a) (f b) _ _
    ((hprod a).trans (hprod b).symm) hc
  · intro x hx
    simpa only [hS', Finset.mem_insert, Finset.mem_singleton] using hs a x hx
  · intro x hx
    simpa only [hS', Finset.mem_insert, Finset.mem_singleton] using hs b x hx

end ArtinMatthews
