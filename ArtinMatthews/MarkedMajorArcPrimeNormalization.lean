module

public import ArtinMatthews.MarkedMajorArcPrimeConversion
public import ArtinMatthews.MarkedMajorArcPartialSummation
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Monotonicity.Lemmas
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

/-! The second, actual partial-summation conversion from reciprocal-prime
normalization to the dyadic scale normalization used by the long coefficient. -/
namespace ArtinMatthews

open Finset
open scoped BigOperators

lemma marked_linear_weight_interval_bound (a : ℕ → ℂ) {H u v D : ℝ}
    (hH : 0 < H) (hHu : H ≤ u) (huv : u ≤ v) (hvH : v ≤ 2*H)
    (hD : 0 ≤ D)
    (hprefix : ∀ w ∈ Set.Icc u v, ‖∑ n ∈ Ioc ⌊u⌋₊ ⌊w⌋₊, a n‖ ≤ D) :
    ‖∑ n ∈ Ioc ⌊u⌋₊ ⌊v⌋₊, ((n:ℝ)/H:ℝ)*(a n)‖ ≤ 5*D := by
  have hu : 0 < u := hH.trans_le hHu
  let c : ℕ → ℂ := fun n => if ⌊u⌋₊ < n then a n else 0
  let φ : ℝ → ℂ := fun x => (x/H:ℝ)
  let φ' : ℝ → ℂ := fun _ => (1/H:ℝ)
  have hd (x : ℝ) (_hx : x ∈ Set.Icc u v) : HasDerivAt φ (φ' x) x := by
    exact ((hasDerivAt_id x).div_const H).ofReal_comp
  have hc : ContinuousOn φ' (Set.Icc u v) := continuousOn_const
  have hval (x : ℝ) (hx : x ∈ Set.Icc u v) : ‖φ x‖ ≤ 2 := by
    have hx0 : 0 < x := hu.trans_le hx.1
    simp only [φ,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (div_pos hx0 hH)]
    exact (div_le_iff₀ hH).mpr (hx.2.trans hvH)
  have hder (x : ℝ) (_hx : x ∈ Set.Icc u v) : ‖φ' x‖ ≤ 1/H := by
    simp only [φ',Complex.norm_real,Real.norm_eq_abs,abs_of_pos (one_div_pos.mpr hH),le_refl]
  have hp (w : ℝ) (hw : w ∈ Set.Icc u v) : ‖∑ n ∈ Icc 0 ⌊w⌋₊, c n‖ ≤ D := by
    simpa only [c,marked_cutoff_prefix_sum a (Nat.floor_mono hw.1)] using hprefix w hw
  have hb := marked_complex_partial_summation_bound c φ φ' hu.le huv hD
    (by norm_num : (0:ℝ)≤2) (by positivity : 0≤1/H) hd hc hval hder hp
  have he : (∑ n ∈ Ioc ⌊u⌋₊ ⌊v⌋₊, φ n*c n) =
      ∑ n ∈ Ioc ⌊u⌋₊ ⌊v⌋₊, ((n:ℝ)/H:ℝ)*(a n) := by
    apply sum_congr rfl
    intro n hn
    simp only [c,ite_eq_left (mem_Ioc.mp hn).1,φ]
  rw [he] at hb
  apply hb.trans
  have hfac : (1/H)*(v-u) ≤ 1 := by
    exact (mul_le_mul_of_nonneg_left (show v-u ≤ H by linarith)
      (by positivity : 0≤1/H)).trans_eq (by field_simp)
  nlinarith

noncomputable def markedMajorNormalizedPrimeSum {q : ℕ} (χ : DirichletCharacter ℂ q)
    (t H u v : ℝ) : ℂ :=
  (1/(H:ℂ))*∑ p ∈ (Ioc ⌊u⌋₊ ⌊v⌋₊).filter Nat.Prime,
    χ (p:ZMod q)*(p:ℂ)^((t:ℂ)*Complex.I)

lemma marked_major_prime_normalization {q : ℕ} (χ : DirichletCharacter ℂ q)
    (t : ℝ) {H u v D : ℝ}
    (hH : 0 < H) (hHu : H ≤ u) (huv : u ≤ v) (hvH : v ≤ 2*H)
    (hD : 0 ≤ D)
    (hprefix : ∀ w ∈ Set.Icc u v, ‖markedMajorPrimeSum χ t u w‖ ≤ D) :
    ‖markedMajorNormalizedPrimeSum χ t H u v‖ ≤ 5*D := by
  classical
  let a : ℕ → ℂ := fun n => if n.Prime then χ (n:ZMod q)*(n:ℂ)^(-1+(t:ℂ)*Complex.I) else 0
  have hp (w : ℝ) (hw : w ∈ Set.Icc u v) : ‖∑ n ∈ Ioc ⌊u⌋₊ ⌊w⌋₊, a n‖ ≤ D := by
    simpa only [markedMajorPrimeSum,sum_filter,a] using hprefix w hw
  have hh := marked_linear_weight_interval_bound a hH hHu huv hvH hD hp
  have he : (∑ n ∈ Ioc ⌊u⌋₊ ⌊v⌋₊, ((n:ℝ)/H:ℝ)*(a n)) =
      markedMajorNormalizedPrimeSum χ t H u v := by
    rw [markedMajorNormalizedPrimeSum,mul_sum,sum_filter]
    apply sum_congr rfl
    intro n hn
    by_cases hnp : n.Prime
    · simp only [a,ite_eq_left hnp]
      have hnC : (n:ℂ) ≠ 0 := by exact_mod_cast hnp.ne_zero
      rw [Complex.cpow_add _ _ hnC,Complex.cpow_neg_one,Complex.ofReal_div,Complex.ofReal_natCast]
      field_simp
    · simp [a,hnp]
  rwa [he] at hh

end ArtinMatthews
