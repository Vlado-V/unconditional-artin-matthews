module

public import Mathlib.Analysis.Complex.Basic
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
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

/-!
# The Cauchy step for removal of the marked divisor weights

These are the finite analytic inequalities used in (2.10) of the
Artin–Matthews manuscript. The prime second-moment bound (2.9) remains a
separate input: none of the statements below assert that sieve estimate.

The finite index set may be the primes in the support of the smooth
cutoff. Set `w p = Φ ((p - 1) / x)` and
`d p = (∑ j, W j (p - 1) / m j) / b - 1`.
-/

namespace ArtinMatthews

/-- Weighted real Cauchy–Schwarz, with weights required nonnegative only
on the finite summation set. -/
theorem marked_weighted_cauchy {ι : Type*} (S : Finset ι) (w d : ι → ℝ)
    (hw : ∀ i ∈ S, 0 ≤ w i) :
    (∑ i ∈ S, w i * |d i|) ≤
      Real.sqrt (∑ i ∈ S, w i) * Real.sqrt (∑ i ∈ S, w i * d i ^ 2) := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt S
    (fun i => Real.sqrt (w i)) (fun i => Real.sqrt (w i) * |d i|)
  have hleft : (∑ i ∈ S, Real.sqrt (w i) * (Real.sqrt (w i) * |d i|)) =
      ∑ i ∈ S, w i * |d i| := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [← mul_assoc, Real.mul_self_sqrt (hw i hi)]
  have hfirst : (∑ i ∈ S, Real.sqrt (w i) ^ 2) = ∑ i ∈ S, w i := by
    apply Finset.sum_congr rfl
    intro i hi
    exact Real.sq_sqrt (hw i hi)
  have hsecond : (∑ i ∈ S, (Real.sqrt (w i) * |d i|) ^ 2) =
      ∑ i ∈ S, w i * d i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [mul_pow, Real.sq_sqrt (hw i hi), sq_abs]
  rwa [hleft, hfirst, hsecond] at h

/-- The exact finite estimate behind (2.10), allowing arbitrary bounded
complex coefficients on the primes. -/
theorem marked_deweighting_bound {ι : Type*} (S : Finset ι)
    (w d : ι → ℝ) (a : ι → ℂ) {C : ℝ}
    (hw : ∀ i ∈ S, 0 ≤ w i) (hC : 0 ≤ C)
    (ha : ∀ i ∈ S, ‖a i‖ ≤ C) :
    ‖∑ i ∈ S, (w i : ℂ) * a i * (d i : ℂ)‖ ≤
      C * Real.sqrt (∑ i ∈ S, w i) * Real.sqrt (∑ i ∈ S, w i * d i ^ 2) := by
  calc
    ‖∑ i ∈ S, (w i : ℂ) * a i * (d i : ℂ)‖ ≤
        ∑ i ∈ S, ‖(w i : ℂ) * a i * (d i : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ S, C * (w i * |d i|) := by
      apply Finset.sum_le_sum
      intro i hi
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw i hi)]
      calc
        w i * ‖a i‖ * |d i| ≤ w i * C * |d i| :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (ha i hi) (hw i hi)) (abs_nonneg _)
        _ = C * (w i * |d i|) := by ring
    _ = C * ∑ i ∈ S, w i * |d i| := (Finset.mul_sum _ _ _).symm
    _ ≤ C * (Real.sqrt (∑ i ∈ S, w i) * Real.sqrt (∑ i ∈ S, w i * d i ^ 2)) :=
      mul_le_mul_of_nonneg_left (marked_weighted_cauchy S w d hw) hC
    _ = _ := by ring

/-- Normalization by `log x / x` can be included in the weights, so bounds
for normalized total prime mass and normalized marked second moment give
the corresponding normalized prime error without further hypotheses. -/
theorem marked_deweighting_of_mass_bounds {ι : Type*} (S : Finset ι)
    (w d : ι → ℝ) (a : ι → ℂ) {C M V : ℝ}
    (hw : ∀ i ∈ S, 0 ≤ w i) (hC : 0 ≤ C)
    (ha : ∀ i ∈ S, ‖a i‖ ≤ C)
    (hM : ∑ i ∈ S, w i ≤ M) (hV : ∑ i ∈ S, w i * d i ^ 2 ≤ V) :
    ‖∑ i ∈ S, (w i : ℂ) * a i * (d i : ℂ)‖ ≤ C * Real.sqrt M * Real.sqrt V := by
  apply (marked_deweighting_bound S w d a hw hC ha).trans
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hM) hC
  · exact Real.sqrt_le_sqrt hV
  · exact Real.sqrt_nonneg _
  · positivity

/-- An analytic transfer form of the finite inequality. If the normalized
second moment vanishes and the normalized total mass remains bounded,
then every uniformly bounded complex test has vanishing deweighting error.
The finite support is allowed to grow with the limiting parameter. -/
theorem marked_deweighting_tendsto {κ ι : Type*} {l : Filter κ}
    (S : κ → Finset ι) (w d : κ → ι → ℝ) (a : κ → ι → ℂ)
    {C M : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ᶠ x in l, (∀ i ∈ S x, 0 ≤ w x i) ∧
      (∀ i ∈ S x, ‖a x i‖ ≤ C) ∧ (∑ i ∈ S x, w x i) ≤ M)
    (hvariance : Filter.Tendsto (fun x => ∑ i ∈ S x, w x i * d x i ^ 2) l
      (nhds 0)) :
    Filter.Tendsto (fun x => ∑ i ∈ S x, (w x i : ℂ) * a x i * (d x i : ℂ))
      l (nhds 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hsmall : Filter.Tendsto
      (fun x => C * Real.sqrt M * Real.sqrt (∑ i ∈ S x, w x i * d x i ^ 2))
      l (nhds 0) := by
    simpa using hvariance.sqrt.const_mul (C * Real.sqrt M)
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) _ hsmall
  filter_upwards [hbound] with x hx
  exact marked_deweighting_of_mass_bounds (S x) (w x) (d x) (a x)
    hx.1 hC hx.2.1 hx.2.2 le_rfl

end ArtinMatthews
