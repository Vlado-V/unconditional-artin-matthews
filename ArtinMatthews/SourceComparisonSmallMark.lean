module

public import ArtinMatthews.GiantCandidateSquareCount
public import ArtinMatthews.SourceComparisonMarkWeight
public import ArtinMatthews.SourceComparisonLiteralMarks
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! Removing the distinguished one-mark group keeps its original reciprocal
mass and its remaining zero-mark damping. Square exceptions are explicit. -/
namespace ArtinMatthews
open Finset Filter
open scoped BigOperators
noncomputable section

variable {G : Type*} [Fintype G]

theorem sourceComparisonActiveDivisors_mul_prime (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) {p : ℕ} (hp : p.Prime) (n : ℕ) :
    activeDivisors P (p * n) = (P ∩ {p}) ∪ activeDivisors P n := by
  classical
  ext r
  simp only [activeDivisors, mem_filter, mem_union, mem_inter, mem_singleton]
  constructor
  · rintro ⟨hr, hd⟩
    rcases (hP r hr).dvd_mul.mp hd with h | h
    · exact Or.inl ⟨hr, (Nat.prime_dvd_prime_iff_eq (hP r hr) hp).mp h⟩
    · exact Or.inr ⟨hr, h⟩
  · rintro (⟨hr, rfl⟩ | ⟨hr, hd⟩)
    · exact ⟨hr, dvd_mul_right _ _⟩
    · exact ⟨hr, dvd_mul_of_dvd_right hd p⟩

theorem sourceComparisonMarkWeight_mul_outside (P : G → Finset ℕ) (t : G → ℕ) (q : G → ℝ)
    (b : ((g : G) → Fin (t g) → ℕ) → ℂ)
    (hP : ∀ g r, r ∈ P g → r.Prime) {p : ℕ} (hp : p.Prime)
    (hout : ∀ g, p ∉ P g) (n : ℕ) :
    sourceComparisonMarkWeight P t q b (p * n) = sourceComparisonMarkWeight P t q b n := by
  have he (g : G) : activeDivisors (P g) (p * n) = activeDivisors (P g) n := by
    rw [sourceComparisonActiveDivisors_mul_prime _ (hP g) hp]
    have hI : P g ∩ {p} = ∅ := by
      ext r
      simp only [mem_inter, mem_singleton, notMem_empty, iff_false]
      rintro ⟨h, rfl⟩
      exact hout g h
    rw [hI, empty_union]
  unfold sourceComparisonMarkWeight sourceComparisonMarkHitDamping bandCount
  simp_rw [he]

def sourceComparisonDistinguishedMarkWeight (S : Finset ℕ) (P : G → Finset ℕ)
    (a : ℕ) (t : G → ℕ) (q₀ : ℝ) (q : G → ℝ)
    (b : ((g : G) → Fin (t g) → ℕ) → ℂ) (n : ℕ) : ℂ :=
  sourceComparisonMarkWeight (Sum.elim (fun _ : Unit => S) P)
    (Sum.elim (fun _ => a) t) (Sum.elim (fun _ => q₀) q)
    (fun l => b (fun g => l (.inr g))) n

theorem sourceComparisonDistinguishedMarkWeight_product (S : Finset ℕ) (P : G → Finset ℕ)
    (a : ℕ) (t : G → ℕ) (q₀ : ℝ) (q : G → ℝ)
    (b : ((g : G) → Fin (t g) → ℕ) → ℂ) (n : ℕ) :
    sourceComparisonDistinguishedMarkWeight S P a t q₀ q b n =
      sourceComparisonMarkWeight (fun _ : Unit => S) (fun _ => a) (fun _ => q₀) (fun _ => 1) n *
        sourceComparisonMarkWeight P t q b n := by
  simpa only [sourceComparisonDistinguishedMarkWeight, one_mul] using
    sourceComparisonMarkWeight_sum (fun _ : Unit => S) P (fun _ => a) t
      (fun _ => q₀) q (fun _ => 1) b n

theorem sourceComparisonDistinguishedMarkWeight_one (S : Finset ℕ) (P : G → Finset ℕ)
    (t : G → ℕ) (q₀ : ℝ) (q : G → ℝ)
    (b : ((g : G) → Fin (t g) → ℕ) → ℂ) (n : ℕ) :
    sourceComparisonDistinguishedMarkWeight S P 1 t q₀ q b n =
      ((bandCount S n : ℂ) / (bandReciprocalMass S : ℂ)) *
        (q₀ : ℂ) ^ (bandCount S n - 1) * sourceComparisonMarkWeight P t q b n := by
  rw [sourceComparisonDistinguishedMarkWeight_product, sourceComparisonMarkWeight_one]
  simp only [Fintype.prod_unique, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_natCast, Complex.ofReal_pow]

theorem sourceComparisonDistinguishedMarkWeight_zero (S : Finset ℕ) (P : G → Finset ℕ)
    (t : G → ℕ) (q₀ : ℝ) (q : G → ℝ)
    (b : ((g : G) → Fin (t g) → ℕ) → ℂ) (n : ℕ) :
    sourceComparisonDistinguishedMarkWeight S P 0 t q₀ q b n =
      (q₀ : ℂ) ^ bandCount S n * sourceComparisonMarkWeight P t q b n := by
  rw [sourceComparisonDistinguishedMarkWeight_product, sourceComparisonMarkWeight_zero]
  simp only [Fintype.prod_unique, Complex.ofReal_pow]

def sourceComparisonRemovedSmallMark (S : Finset ℕ) (P : G → Finset ℕ)
    (t : G → ℕ) (q₀ : ℝ) (q : G → ℝ)
    (b : ((g : G) → Fin (t g) → ℕ) → ℂ) (n : ℕ) : ℂ :=
  (bandReciprocalMass S : ℂ)⁻¹ * ∑ p ∈ activeDivisors S n,
    sourceComparisonDistinguishedMarkWeight S P 0 t q₀ q b (n / p)

theorem sourceComparisonOneSmallMark_removal (S : Finset ℕ) (P : G → Finset ℕ)
    (t : G → ℕ) (q₀ : ℝ) (q : G → ℝ)
    (b : ((g : G) → Fin (t g) → ℕ) → ℂ)
    (hS : ∀ p ∈ S, p.Prime) (hP : ∀ g p, p ∈ P g → p.Prime)
    (hdis : ∀ g, Disjoint S (P g)) (n : ℕ) (hsq : ∀ p ∈ S, ¬ p ^ 2 ∣ n) :
    sourceComparisonDistinguishedMarkWeight S P 1 t q₀ q b n =
      sourceComparisonRemovedSmallMark S P t q₀ q b n := by
  classical
  have hterm (p : ℕ) (hp : p ∈ activeDivisors S n) :
      sourceComparisonDistinguishedMarkWeight S P 0 t q₀ q b (n / p) =
        (q₀ : ℂ) ^ (bandCount S n - 1) * sourceComparisonMarkWeight P t q b n := by
    obtain ⟨hpS, hpn⟩ := mem_filter.mp hp
    have he : p * (n / p) = n := Nat.mul_div_cancel' hpn
    have hnp : ¬ p ∣ n / p := by
      intro h
      apply hsq p hpS
      rw [pow_two, ← he]
      exact Nat.mul_dvd_mul_left p h
    have hc : bandCount S n - 1 = bandCount S (n / p) := by
      unfold bandCount
      have hhit := sourceComparisonActiveDivisors_mul_prime S hS (hS p hpS) (n / p)
      rw [he] at hhit
      have hI : S ∩ {p} = {p} := inter_eq_right.mpr (singleton_subset_iff.mpr hpS)
      have hmem : p ∉ activeDivisors S (n / p) := fun hm => hnp (mem_filter.mp hm).2
      rw [hhit, hI, singleton_union, card_insert_of_notMem hmem]
      omega
    have hout (g : G) : p ∉ P g := fun h => disjoint_left.mp (hdis g) hpS h
    have hrest := sourceComparisonMarkWeight_mul_outside P t q b hP (hS p hpS) hout (n / p)
    rw [he] at hrest
    rw [sourceComparisonDistinguishedMarkWeight_zero, ← hc, ← hrest]
  rw [sourceComparisonDistinguishedMarkWeight_one, sourceComparisonRemovedSmallMark]
  have hsum : (∑ p ∈ activeDivisors S n,
      sourceComparisonDistinguishedMarkWeight S P 0 t q₀ q b (n / p)) =
      ∑ _p ∈ activeDivisors S n, (q₀ : ℂ) ^ (bandCount S n - 1) *
        sourceComparisonMarkWeight P t q b n := sum_congr rfl (fun p hp => hterm p hp)
  rw [hsum, sum_const, nsmul_eq_mul]
  unfold bandCount
  ring

theorem sourceComparisonOneSmallMark_removal_of_not_exception (S : Finset ℕ) (P : G → Finset ℕ)
    (t : G → ℕ) (q₀ : ℝ) (q : G → ℝ)
    (b : ((g : G) → Fin (t g) → ℕ) → ℂ)
    (hS : ∀ p ∈ S, p.Prime) (hP : ∀ g p, p ∈ P g → p.Prime)
    (hdis : ∀ g, Disjoint S (P g)) {n N : ℕ} (hn : n ∈ Ioc 0 N)
    (hbad : n ∉ giantCandidateSquareExceptions S N) :
    sourceComparisonDistinguishedMarkWeight S P 1 t q₀ q b n =
      sourceComparisonRemovedSmallMark S P t q₀ q b n := by
  apply sourceComparisonOneSmallMark_removal S P t q₀ q b hS hP hdis n
  intro p hp hsq
  exact hbad (mem_giantCandidateSquareExceptions.mpr
    ⟨(mem_Ioc.mp hn).1, (mem_Ioc.mp hn).2, p, hp, hsq⟩)

theorem sourceComparisonOneSmallMark_square_error (S : Finset ℕ) (P : G → Finset ℕ)
    (t : G → ℕ) (q₀ : ℝ) (q : G → ℝ)
    (b : ((g : G) → Fin (t g) → ℕ) → ℂ)
    (hS : ∀ p ∈ S, p.Prime) (hP : ∀ g p, p ∈ P g → p.Prime)
    (hdis : ∀ g, Disjoint S (P g)) (N : ℕ) (B : ℝ)
    (hB : ∀ n ∈ Ioc 0 N, ‖sourceComparisonDistinguishedMarkWeight S P 1 t q₀ q b n -
      sourceComparisonRemovedSmallMark S P t q₀ q b n‖ ≤ B) :
    (∑ n ∈ Ioc 0 N, ‖sourceComparisonDistinguishedMarkWeight S P 1 t q₀ q b n -
      sourceComparisonRemovedSmallMark S P t q₀ q b n‖ ^ 2) ≤
      ((N : ℝ) * ∑ p ∈ S, 1 / (p : ℝ) ^ 2) * B ^ 2 := by
  classical
  let bad := giantCandidateSquareExceptions S N
  have hs : bad ⊆ Ioc 0 N := fun _ hn =>
    mem_Ioc.mpr ⟨(mem_giantCandidateSquareExceptions.mp hn).1,
      (mem_giantCandidateSquareExceptions.mp hn).2.1⟩
  rw [← sum_subset hs (fun n hn hbad => by
    rw [sourceComparisonOneSmallMark_removal_of_not_exception S P t q₀ q b hS hP hdis hn hbad]
    simp)]
  calc
    _ ≤ ∑ _n ∈ bad, B ^ 2 := by
      apply sum_le_sum
      intro n hn
      exact pow_le_pow_left₀ (norm_nonneg _) (hB n (hs hn)) 2
    _ = (bad.card : ℝ) * B ^ 2 := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (giantCandidateSquareExceptions_card_le S N) (sq_nonneg _)


theorem sourceComparisonSmallGroup_squareCount_eventually :
    ∀ᶠ x : ℝ in atTop, ∀ g : GiantCandidateSmallGroupIndex x, ∀ N : ℕ,
      ((giantCandidateSquareExceptions (giantCandidateSmallGroup x g) N).card : ℝ) ≤
        4 * (N : ℝ) * Real.exp (-(Real.log x) ^ (28 / 100 : ℝ)) := by
  filter_upwards [giantCandidateSquareExceptions_actual_card_eventually] with x hx
  intro g N
  have hg : giantCandidateSmallGroup x g ⊆ giantCandidateFullPrimes x := by
    intro p hp
    exact mem_biUnion.mpr ⟨Sum.inl g, mem_univ _, hp⟩
  have hs : giantCandidateSquareExceptions (giantCandidateSmallGroup x g) N ⊆
      giantCandidateSquareExceptions (giantCandidateFullPrimes x) N := by
    intro n hn
    obtain ⟨h0, hN, p, hp, hd⟩ := mem_giantCandidateSquareExceptions.mp hn
    exact mem_giantCandidateSquareExceptions.mpr ⟨h0, hN, p, hg hp, hd⟩
  exact (by exact_mod_cast card_le_card hs :
    ((giantCandidateSquareExceptions (giantCandidateSmallGroup x g) N).card : ℝ) ≤
      (giantCandidateSquareExceptions (giantCandidateFullPrimes x) N).card).trans (hx N)

end
end ArtinMatthews
