module

public import ArtinMatthews.PrimeExtractionDyadicPartition
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


set_option backward.privateInPublic true
@[expose] public section

/-! Exact active dyadic boxes for a hyperbola-supported finite sum. -/

namespace ArtinMatthews
open scoped BigOperators

def primeExtractionDyadicIndexPairs (N : ℕ) : Finset (ℕ × ℕ) :=
  Finset.range (Nat.log 2 N + 1) ×ˢ Finset.range (Nat.log 2 N + 1)

def primeExtractionDyadicActive (N : ℕ) : Finset (ℕ × ℕ) :=
  (primeExtractionDyadicIndexPairs N).filter (fun kl => 2^kl.1 * 2^kl.2 ≤ N)

def primeExtractionDyadicHeight (k l : ℕ) : ℝ := ((2^k * 2^l : ℕ) : ℝ)

theorem primeExtractionDyadicProduct_bounds {N k l m n : ℕ}
    (hm : m ∈ primeExtractionDyadicBlock N k)
    (hn : n ∈ primeExtractionDyadicBlock N l) :
    2^k * 2^l ≤ m*n ∧ m*n < 4*(2^k * 2^l) := by
  obtain ⟨hmlo, hmhi⟩ := primeExtractionDyadicBlock_bounds hm
  obtain ⟨hnlo, hnhi⟩ := primeExtractionDyadicBlock_bounds hn
  refine ⟨Nat.mul_le_mul hmlo hnlo, ?_⟩
  have hn0 : 0 < n := lt_of_lt_of_le (by positivity : 0 < 2^l) hnlo
  calc
    m*n < (2*2^k)*n := mul_lt_mul_of_pos_right hmhi hn0
    _ < (2*2^k)*(2*2^l) := mul_lt_mul_of_pos_left hnhi (by positivity)
    _ = _ := by ring

theorem primeExtractionDyadicBox_eq_zero {R : Type*} [AddCommMonoid R]
    (N k l : ℕ) (F : ℕ → ℕ → R)
    (hF : ∀ m n, N < m*n → F m n = 0) (hheight : N < 2^k * 2^l) :
    (∑ m ∈ primeExtractionDyadicBlock N k,
      ∑ n ∈ primeExtractionDyadicBlock N l, F m n) = 0 := by
  apply Finset.sum_eq_zero
  intro m hm
  apply Finset.sum_eq_zero
  intro n hn
  exact hF m n (hheight.trans_le (primeExtractionDyadicProduct_bounds hm hn).1)

/-- Every original summand is retained, while boxes above the hyperbola
are removed only after their actual summands have been proved zero. -/
theorem prime_extraction_dyadic_supported_sum {R : Type*} [AddCommMonoid R]
    (N : ℕ) (F : ℕ → ℕ → R) (hF : ∀ m n, N < m*n → F m n = 0) :
    (∑ m ∈ Finset.Ioc 0 N, ∑ n ∈ Finset.Ioc 0 N, F m n) =
      ∑ kl ∈ primeExtractionDyadicActive N,
        ∑ m ∈ primeExtractionDyadicBlock N kl.1,
          ∑ n ∈ primeExtractionDyadicBlock N kl.2, F m n := by
  classical
  calc
    _ = ∑ k ∈ Finset.range (Nat.log 2 N+1), ∑ l ∈ Finset.range (Nat.log 2 N+1),
        ∑ m ∈ primeExtractionDyadicBlock N k,
          ∑ n ∈ primeExtractionDyadicBlock N l, F m n := prime_extraction_dyadic_double_sum N F
    _ = ∑ kl ∈ primeExtractionDyadicIndexPairs N,
        ∑ m ∈ primeExtractionDyadicBlock N kl.1,
          ∑ n ∈ primeExtractionDyadicBlock N kl.2, F m n := by
      rw [primeExtractionDyadicIndexPairs, Finset.sum_product]
    _ = _ := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro kl hkl hnot
      apply primeExtractionDyadicBox_eq_zero N kl.1 kl.2 F hF
      by_contra hh
      exact hnot (Finset.mem_filter.mpr ⟨hkl, by omega⟩)

theorem primeExtractionDyadicActive_card_le (N : ℕ) :
    (primeExtractionDyadicActive N).card ≤ (Nat.log 2 N+1)^2 := by
  apply (Finset.card_filter_le _ _).trans_eq
  simp only [primeExtractionDyadicIndexPairs, Finset.card_product, Finset.card_range, pow_two]

theorem primeExtractionDyadicActive_count_le (N : ℕ) :
    ((primeExtractionDyadicActive N).card : ℝ) ≤
      (1+Real.log (N+1)/Real.log 2)^2 := by
  have hcard : ((primeExtractionDyadicActive N).card : ℝ) ≤
      ((Nat.log 2 N+1 : ℕ) : ℝ)^2 := by
    exact_mod_cast primeExtractionDyadicActive_card_le N
  exact hcard.trans (pow_le_pow_left₀ (Nat.cast_nonneg _)
    (primeExtractionDyadicIndex_count_le N) 2)

/-- The genuine cutoff support forces both sides of the product scale.
This remains available before Mellin separation removes the cutoff. -/
theorem primeExtractionDyadicCutoff_height {N k l m n : ℕ} {Φ : ℝ → ℂ} {a b x : ℝ}
    (hx : 0 < x) (hsupp : Function.support Φ ⊆ Set.Icc a b)
    (hm : m ∈ primeExtractionDyadicBlock N k) (hn : n ∈ primeExtractionDyadicBlock N l)
    (hΦ : Φ (((m*n : ℕ) : ℝ)/x) ≠ 0) :
    primeExtractionDyadicHeight k l ≤ b*x ∧ a*x ≤ 4*primeExtractionDyadicHeight k l := by
  have harg := hsupp hΦ
  have hprod := primeExtractionDyadicProduct_bounds hm hn
  have hlow : a*x ≤ ((m*n : ℕ) : ℝ) := (le_div_iff₀ hx).mp harg.1
  have hhigh : ((m*n : ℕ) : ℝ) ≤ b*x := (div_le_iff₀ hx).mp harg.2
  have hdyadlo : primeExtractionDyadicHeight k l ≤ ((m*n : ℕ) : ℝ) := by
    unfold primeExtractionDyadicHeight
    exact_mod_cast hprod.1
  have hdyadhi : ((m*n : ℕ) : ℝ) ≤ 4*primeExtractionDyadicHeight k l := by
    unfold primeExtractionDyadicHeight
    exact_mod_cast hprod.2.le
  exact ⟨hdyadlo.trans hhigh, hlow.trans hdyadhi⟩

theorem primeExtractionDyadicCutoff_zero_of_height {N k l m n : ℕ}
    {Φ : ℝ → ℂ} {a b x : ℝ} (hx : 0 < x) (hsupp : Function.support Φ ⊆ Set.Icc a b)
    (hm : m ∈ primeExtractionDyadicBlock N k) (hn : n ∈ primeExtractionDyadicBlock N l)
    (hheight : b*x < primeExtractionDyadicHeight k l ∨
      4*primeExtractionDyadicHeight k l < a*x) :
    Φ (((m*n : ℕ) : ℝ)/x) = 0 := by
  by_contra hΦ
  have hh := primeExtractionDyadicCutoff_height hx hsupp hm hn hΦ
  rcases hheight with h | h <;> linarith

end ArtinMatthews
