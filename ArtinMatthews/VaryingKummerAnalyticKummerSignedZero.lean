module

public import ArtinMatthews.VaryingKummerAnalyticSplitPrimeSignedZero
public import ArtinMatthews.Index
public import ArtinMatthews.KummerSplittingDiscriminantBasis
public import ArtinMatthews.KummerSplittingPrimeIdeals
public import ArtinMatthews.ReciprocalTail
public import ArtinMatthews.VaryingKummerAnalyticKummerSplitEstimate
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual varying-prime splitting count, with its signed zero loss
retained exactly. The constant is independent of q; summing over q preserves
the signed losses instead of replacing them by an unproved power saving. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField OAI.PrimeDegreePackets Complex
open scoped Classical BigOperators
noncomputable section

theorem exists_primeKummer_split_signed_zero_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℤ), a ≠ 0 → a ≠ 1 → a ≠ -1 →
      ∀ (q : ℕ), q.Prime → a.natAbs ≤ q → ∀ (x : ℝ) (S : Finset Nat.Primes), 1 < x →
      (∀ p ∈ S, x ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2*x ∧
        ¬ (p.val : ℤ) ∣ (q : ℤ) ∧ (a : ZMod p.val) ≠ 0 ∧ q ∣ multiplicativeIndex p a) →
      (S.card : ℝ) + (splitPrimeMellinZeroSum (primeKummerField q a) x).re /
        ((q : ℝ)*((q : ℝ)-1)*Real.log x) ≤
      C*(x/((q : ℝ)*((q : ℝ)-1)*Real.log x) + Real.log (2*(q : ℝ))/Real.log x) := by
  obtain ⟨C,hC,HC⟩ := exists_splitPrime_count_signed_zero_bound.{0}
  refine ⟨14*C,by positivity,?_⟩
  intro a ha0 ha1 ham1 q hq haq x S hx hS
  let : NeZero q := ⟨hq.ne_zero⟩
  let : NeZero a := ⟨ha0⟩
  let n : ℝ := Module.finrank ℚ (primeKummerField q a)
  let d : ℝ := Real.log |(discr (primeKummerField q a):ℝ)|+n
  have hn : 0 < n := by
    dsimp [n]
    exact_mod_cast Module.finrank_pos (R := ℚ) (M := primeKummerField q a)
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hden : 0 < n*Real.log x := mul_pos hn hlog
  have hN : n = (q : ℝ)*((q : ℝ)-1) := by
    dsimp [n]
    rw [finrank_primeKummerField_of_large_prime ha0 ha1 ham1 hq haq]
    push_cast [Nat.cast_sub hq.one_lt.le]
    ring
  have H := HC (primeKummerField q a) x S hx
    (fun p hp => ⟨(hS p hp).1,(hS p hp).2.1⟩)
    (fun p hp => primeKummer_normFiber_card_of_dvd_index p.property
      (hS p hp).2.2.1 (hS p hp).2.2.2.1 (hS p hp).2.2.2.2)
  have hd : d ≤ 14*n*Real.log (2*(q : ℝ)) :=
    primeKummer_log_discr_add_degree_le ha0 ha1 ham1 hq haq
  have hCd := mul_le_mul_of_nonneg_left hd hC.le
  have hx0 : 0 ≤ x := (zero_lt_one.trans hx).le
  rw [← hN]
  calc
    _ = ((S.card : ℝ)*n*Real.log x +
        (splitPrimeMellinZeroSum (primeKummerField q a) x).re)/(n*Real.log x) := by
      field_simp
    _ ≤ (C*x+C*d)/(n*Real.log x) := div_le_div_of_nonneg_right H hden.le
    _ ≤ (14*C*x+14*C*n*Real.log (2*(q : ℝ)))/(n*Real.log x) := by
      apply div_le_div_of_nonneg_right _ hden.le
      nlinarith [mul_nonneg hC.le hx0]
    _ = _ := by field_simp

theorem exists_primeKummer_aggregate_signed_zero_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℤ), a ≠ 0 → a ≠ 1 → a ≠ -1 →
      ∀ (P : Finset ℕ) (Y : ℕ) (x : ℝ) (S : ℕ → Finset Nat.Primes), 0 < Y → 1 < x →
      (∀ q ∈ P, q.Prime ∧ a.natAbs ≤ q ∧ Y < q) →
      (∀ q ∈ P, ∀ p ∈ S q, x ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2*x ∧
        ¬ (p.val : ℤ) ∣ (q : ℤ) ∧ (a : ZMod p.val) ≠ 0 ∧ q ∣ multiplicativeIndex p a) →
      (∑ q ∈ P, ((S q).card : ℝ)) +
        (∑ q ∈ P, (splitPrimeMellinZeroSum (primeKummerField q a) x).re /
          ((q : ℝ)*((q : ℝ)-1)*Real.log x)) ≤
      C*(x/((Y : ℝ)*Real.log x) + (∑ q ∈ P, Real.log (2*(q : ℝ)))/Real.log x) := by
  obtain ⟨C,hC,HC⟩ := exists_primeKummer_split_signed_zero_bound
  refine ⟨C,hC,?_⟩
  intro a ha0 ha1 ham1 P Y x S hY hx hP hS
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hx0 : 0 ≤ x/Real.log x := div_nonneg (zero_lt_one.trans hx).le hlog.le
  have hrec := sum_reciprocal_tail_le P Y hY (fun q hq => (hP q hq).2.2)
  have H := Finset.sum_le_sum (s := P) (fun q hq =>
    HC a ha0 ha1 ham1 q (hP q hq).1 (hP q hq).2.1 x (S q) hx (hS q hq))
  rw [Finset.sum_add_distrib] at H
  calc
    _ ≤ ∑ q ∈ P, C*(x/((q : ℝ)*((q : ℝ)-1)*Real.log x) +
        Real.log (2*(q : ℝ))/Real.log x) := H
    _ = C*((x/Real.log x)*(∑ q ∈ P, 1/((q : ℝ)*((q : ℝ)-1))) +
        (∑ q ∈ P, Real.log (2*(q : ℝ)))/Real.log x) := by
      rw [← Finset.mul_sum,Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_div]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    _ ≤ C*((x/Real.log x)*(1/(Y : ℝ)) +
        (∑ q ∈ P, Real.log (2*(q : ℝ)))/Real.log x) :=
      mul_le_mul_of_nonneg_left (add_le_add
        (mul_le_mul_of_nonneg_left hrec hx0) le_rfl) hC.le
    _ = _ := by simp only [div_eq_mul_inv,mul_inv_rev]; ring

end
end ArtinMatthews.VaryingKummerAnalytic
