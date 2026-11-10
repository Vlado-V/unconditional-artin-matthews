module

public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import ArtinMatthews.MarkedMajorArcPartialSummation
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

/-! Exact smooth logarithmic-phase removal on dyadic intervals. The input
is an actual sharp-prefix bound for the centered arithmetic coefficients. -/
namespace ArtinMatthews
open Finset

 theorem marked_log_phase_interval_bound (a : ℕ → ℂ) (t : ℝ) {u v D : ℝ}
    (hu : 0 < u) (hlog : 1 ≤ Real.log u) (huv : u ≤ v) (hvu : v ≤ 2*u)
    (hD : 0 ≤ D)
    (hprefix : ∀ w ∈ Set.Icc u v, ‖∑ n ∈ Ioc ⌊u⌋₊ ⌊w⌋₊, a n‖ ≤ D) :
    ‖∑ n ∈ Ioc ⌊u⌋₊ ⌊v⌋₊, ((Real.log n)⁻¹:ℝ)*(n:ℂ)^((t:ℂ)*Complex.I)*a n‖ ≤
      D*(|t|+3) := by
  let c : ℕ → ℂ := fun n => if ⌊u⌋₊ < n then a n else 0
  let z : ℂ := (t:ℂ)*Complex.I
  let φ : ℝ → ℂ := fun x => ((Real.log x)⁻¹:ℝ)*(x:ℂ)^z
  let φ' : ℝ → ℂ := fun x =>
    (-x⁻¹/(Real.log x)^2:ℝ)*(x:ℂ)^z + ((Real.log x)⁻¹:ℝ)*(z*(x:ℂ)^(z-1))
  have hxpos (x : ℝ) (hx : x ∈ Set.Icc u v) : 0 < x := hu.trans_le hx.1
  have hxlog (x : ℝ) (hx : x ∈ Set.Icc u v) : 1 ≤ Real.log x :=
    hlog.trans (Real.log_le_log hu hx.1)
  have hlogpos (x : ℝ) (hx : x ∈ Set.Icc u v) : 0 < Real.log x := by linarith [hxlog x hx]
  have hcpow (s : ℂ) (x : ℝ) (hx : x ∈ Set.Icc u v) :
      HasDerivAt (fun y : ℝ => (y:ℂ)^s) (s*(x:ℂ)^(s-1)) x :=
    (Complex.hasStrictDerivAt_cpow_const (Complex.ofReal_mem_slitPlane.mpr (hxpos x hx))).hasDerivAt.comp_ofReal
  have hd (x : ℝ) (hx : x ∈ Set.Icc u v) : HasDerivAt φ (φ' x) x :=
    (((Real.hasDerivAt_log (hxpos x hx).ne').inv (hlogpos x hx).ne').ofReal_comp).mul (hcpow z x hx)
  have hc : ContinuousOn φ' (Set.Icc u v) := by
    intro x hx
    have hloginv : ContinuousAt (fun x : ℝ => ((Real.log x)⁻¹:ℝ)) x :=
      (Real.continuousAt_log (hxpos x hx).ne').inv₀ (hlogpos x hx).ne'
    have hlogderiv : ContinuousAt (fun x : ℝ => (-x⁻¹/(Real.log x)^2:ℝ)) x :=
      ((continuousAt_id.inv₀ (hxpos x hx).ne').neg).div
        ((Real.continuousAt_log (hxpos x hx).ne').pow 2) (pow_ne_zero 2 (hlogpos x hx).ne')
    exact ((Complex.continuous_ofReal.continuousAt.comp hlogderiv).mul (hcpow z x hx).continuousAt |>.add
      ((Complex.continuous_ofReal.continuousAt.comp hloginv).mul
        (continuousAt_const.mul (hcpow (z-1) x hx).continuousAt))).continuousWithinAt
  have hnorm (x : ℝ) (hx : x ∈ Set.Icc u v) : ‖(x:ℂ)^z‖ = 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (hxpos x hx)]
    simp [z]
  have hnorm' (x : ℝ) (hx : x ∈ Set.Icc u v) : ‖(x:ℂ)^(z-1)‖ = x⁻¹ := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (hxpos x hx)]
    simp [z,Real.rpow_neg_one]
  have hval (x : ℝ) (hx : x ∈ Set.Icc u v) : ‖φ x‖ ≤ 1 := by
    simp only [φ,norm_mul,hnorm x hx,mul_one,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (hlogpos x hx))]
    exact inv_le_one_of_one_le₀ (hxlog x hx)
  have hder (x : ℝ) (hx : x ∈ Set.Icc u v) : ‖φ' x‖ ≤ (|t|+1)/u := by
    have hx0 : 0 < x := hxpos x hx
    have hsq : 1 ≤ (Real.log x)^2 := by nlinarith [hxlog x hx]
    have hlinv : (Real.log x)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (hxlog x hx)
    have hxu : x⁻¹ ≤ u⁻¹ := inv_anti₀ hu hx.1
    have hznorm : ‖z‖ = |t| := by simp [z]
    calc
      _ ≤ ‖(-x⁻¹/(Real.log x)^2:ℝ)*(x:ℂ)^z‖+
          ‖((Real.log x)⁻¹:ℝ)*(z*(x:ℂ)^(z-1))‖ := norm_add_le _ _
      _ = x⁻¹/(Real.log x)^2+(Real.log x)⁻¹*(|t| *x⁻¹) := by
        simp only [norm_mul,hnorm x hx,hnorm' x hx,hznorm,mul_one,Complex.norm_real,
          Real.norm_eq_abs,abs_div,abs_neg,abs_of_pos (inv_pos.mpr (hxpos x hx)),
          abs_of_nonneg (sq_nonneg (Real.log x)),abs_of_pos (inv_pos.mpr (hlogpos x hx))]
      _ ≤ x⁻¹+1*(|t| *x⁻¹) := add_le_add (div_le_self (by positivity) hsq)
        (mul_le_mul_of_nonneg_right hlinv (by positivity))
      _ ≤ u⁻¹+1*(|t| *u⁻¹) := by gcongr
      _ = _ := by ring
  have hp (w : ℝ) (hw : w ∈ Set.Icc u v) : ‖∑ n ∈ Icc 0 ⌊w⌋₊, c n‖ ≤ D := by
    simpa only [c,marked_cutoff_prefix_sum a (Nat.floor_mono hw.1)] using hprefix w hw
  have hb := marked_complex_partial_summation_bound c φ φ' hu.le huv hD
    (by norm_num : (0:ℝ)≤1) (by positivity : 0≤(|t|+1)/u) hd hc hval hder hp
  have he : (∑ n ∈ Ioc ⌊u⌋₊ ⌊v⌋₊, φ n*c n) =
      ∑ n ∈ Ioc ⌊u⌋₊ ⌊v⌋₊, ((Real.log n)⁻¹:ℝ)*(n:ℂ)^((t:ℂ)*Complex.I)*a n := by
    apply sum_congr rfl
    intro n hn
    simp only [c,ite_eq_left (mem_Ioc.mp hn).1,φ,z,Complex.ofReal_natCast]
  rw [he] at hb
  apply hb.trans
  have hratio : ((|t|+1)/u)*(v-u) ≤ |t|+1 := by
    apply (mul_le_mul_of_nonneg_left (show v-u≤u by linarith) (by positivity)).trans_eq
    field_simp
  nlinarith

end ArtinMatthews
