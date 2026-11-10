module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
public import Mathlib.NumberTheory.Chebyshev
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


set_option backward.privateInPublic true
@[expose] public section

/-! Literal partial summation for the prime logarithmic weight. The finite
complex Abel bound is extracted from the existing JointDickman proof. -/
namespace ArtinMatthews

open Finset MeasureTheory

theorem marked_complex_partial_summation_bound (c : ℕ → ℂ) (φ φ' : ℝ → ℂ)
    {a b D M N : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (_hD : 0 ≤ D) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hφ : ∀ t ∈ Set.Icc a b, HasDerivAt φ (φ' t) t)
    (hφ' : ContinuousOn φ' (Set.Icc a b))
    (hvalue : ∀ t ∈ Set.Icc a b, ‖φ t‖ ≤ M)
    (hderiv : ∀ t ∈ Set.Icc a b, ‖φ' t‖ ≤ N)
    (hpartial : ∀ t ∈ Set.Icc a b, ‖∑ n ∈ Icc 0 ⌊t⌋₊, c n‖ ≤ D) :
    ‖∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, φ n*c n‖ ≤ D*(2*M+N*(b-a)) := by
  have hd : ContinuousOn (deriv φ) (Set.Icc a b) :=
    hφ'.congr (fun t ht => (hφ t ht).deriv)
  have he := sum_mul_eq_sub_sub_integral_mul (c := c) ha hab
    (fun t ht => (hφ t ht).differentiableAt) hd.integrableOn_Icc
  rw [← intervalIntegral.integral_of_le hab] at he
  have hint : ‖∫ t in a..b, deriv φ t*(∑ n ∈ Icc 0 ⌊t⌋₊, c n)‖ ≤ N*D*(b-a) := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a) (b := b) (f := fun t => deriv φ t*(∑ n ∈ Icc 0 ⌊t⌋₊, c n))
      (C := N*D) (fun t ht => by
        have ht' : t ∈ Set.Icc a b := Set.uIcc_of_le hab ▸ Set.uIoc_subset_uIcc ht
        rw [(hφ t ht').deriv,norm_mul]
        exact mul_le_mul (hderiv t ht') (hpartial t ht') (norm_nonneg _) hN)
    simpa only [abs_of_nonneg (sub_nonneg.mpr hab)] using hh
  have hend (t : ℝ) (ht : t ∈ Set.Icc a b) :
      ‖φ t*(∑ n ∈ Icc 0 ⌊t⌋₊, c n)‖ ≤ M*D := by
    rw [norm_mul]
    exact mul_le_mul (hvalue t ht) (hpartial t ht) (norm_nonneg _) hM
  rw [he]
  calc
    _ ≤ ‖φ b*(∑ n ∈ Icc 0 ⌊b⌋₊, c n)‖ +
        ‖φ a*(∑ n ∈ Icc 0 ⌊a⌋₊, c n)‖ +
        ‖∫ t in a..b, deriv φ t*(∑ n ∈ Icc 0 ⌊t⌋₊, c n)‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ M*D+M*D+N*D*(b-a) :=
      add_le_add (add_le_add (hend b ⟨hab,le_rfl⟩) (hend a ⟨le_rfl,hab⟩)) hint
    _ = _ := by ring


lemma marked_cutoff_prefix_sum (a : ℕ → ℂ) {m n : ℕ} (_hmn : m ≤ n) :
    (∑ k ∈ Icc 0 n, if m < k then a k else 0) = ∑ k ∈ Ioc m n, a k := by
  classical
  have he : (Icc 0 n).filter (fun k => m < k) = Ioc m n := by
    ext k
    simp only [mem_filter,mem_Icc,mem_Ioc]
    omega
  rw [← he,sum_filter]

/-- On a dyadic interval above `e`, removal of a logarithmic weight costs
at most an absolute factor three, using actual sharp prefix sums. -/
theorem marked_log_weight_interval_bound (a : ℕ → ℂ) {u v D : ℝ}
    (hu : 0 < u) (hlog : 1 ≤ Real.log u) (huv : u ≤ v) (hvu : v ≤ 2*u)
    (hD : 0 ≤ D)
    (hprefix : ∀ w ∈ Set.Icc u v, ‖∑ n ∈ Ioc ⌊u⌋₊ ⌊w⌋₊, a n‖ ≤ D) :
    ‖∑ n ∈ Ioc ⌊u⌋₊ ⌊v⌋₊, ((Real.log n)⁻¹:ℝ)*(a n)‖ ≤ 3*D := by
  let c : ℕ → ℂ := fun n => if ⌊u⌋₊ < n then a n else 0
  let φ : ℝ → ℂ := fun x => ((Real.log x)⁻¹:ℝ)
  let φ' : ℝ → ℂ := fun x => (-x⁻¹/(Real.log x)^2:ℝ)
  have hxpos (x : ℝ) (hx : x ∈ Set.Icc u v) : 0 < x := hu.trans_le hx.1
  have hxlog (x : ℝ) (hx : x ∈ Set.Icc u v) : 1 ≤ Real.log x :=
    hlog.trans (Real.log_le_log hu hx.1)
  have hd (x : ℝ) (hx : x ∈ Set.Icc u v) : HasDerivAt φ (φ' x) x := by
    exact ((Real.hasDerivAt_log (hxpos x hx).ne').inv (by linarith [hxlog x hx])).ofReal_comp
  have hc : ContinuousOn φ' (Set.Icc u v) := by
    intro x hx
    have hlogne : Real.log x ≠ 0 := by linarith [hxlog x hx]
    exact (Complex.continuous_ofReal.continuousAt.comp
      (((continuousAt_id.inv₀ (hxpos x hx).ne').neg).div
        ((Real.continuousAt_log (hxpos x hx).ne').pow 2) (pow_ne_zero 2 hlogne))).continuousWithinAt
  have hval (x : ℝ) (hx : x ∈ Set.Icc u v) : ‖φ x‖ ≤ 1 := by
    have hlogp : 0 < Real.log x := by linarith [hxlog x hx]
    simp only [φ,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hlogp)]
    exact inv_le_one_of_one_le₀ (hxlog x hx)
  have hder (x : ℝ) (hx : x ∈ Set.Icc u v) : ‖φ' x‖ ≤ 1/u := by
    have hlogp : 0 < Real.log x := by linarith [hxlog x hx]
    have hsq : 1 ≤ (Real.log x)^2 := by nlinarith [hxlog x hx]
    simp only [φ',Complex.norm_real,Real.norm_eq_abs,abs_div,abs_neg,
      abs_of_pos (inv_pos.mpr (hxpos x hx)),abs_of_nonneg (sq_nonneg (Real.log x))]
    exact (div_le_self (inv_nonneg.mpr (hxpos x hx).le) hsq).trans
      (by simpa only [one_div] using one_div_le_one_div_of_le hu hx.1)
  have hp (w : ℝ) (hw : w ∈ Set.Icc u v) : ‖∑ n ∈ Icc 0 ⌊w⌋₊, c n‖ ≤ D := by
    simpa only [c,marked_cutoff_prefix_sum a (Nat.floor_mono hw.1)] using hprefix w hw
  have hb := marked_complex_partial_summation_bound c φ φ' hu.le huv hD
    (by norm_num : (0:ℝ)≤1) (by positivity : 0≤1/u) hd hc hval hder hp
  have he : (∑ n ∈ Ioc ⌊u⌋₊ ⌊v⌋₊, φ n*c n) =
      ∑ n ∈ Ioc ⌊u⌋₊ ⌊v⌋₊, ((Real.log n)⁻¹:ℝ)*(a n) := by
    apply sum_congr rfl
    intro n hn
    simp only [c,ite_eq_left (mem_Ioc.mp hn).1,φ]
  rw [he] at hb
  apply hb.trans
  have hfac : (1/u)*(v-u) ≤ 1 := by
    exact (mul_le_mul_of_nonneg_left (show v-u ≤ u by linarith)
      (by positivity : 0≤1/u)).trans_eq (by field_simp)
  nlinarith

end ArtinMatthews
