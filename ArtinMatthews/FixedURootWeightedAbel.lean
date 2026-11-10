module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
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

/-! Finite smooth-weight estimates from actual rectangle discrepancies.
The prefix counts below retain each atom and all boundary contributions. -/

noncomputable section
namespace ArtinMatthews
open MeasureTheory
open scoped BigOperators

def rootWeightVariation (f : ℝ → ℂ) (a b : ℝ) : ℝ :=
  ‖f a‖ + ∫ t in Set.Ioc a b, ‖deriv f t‖

theorem rootWeightVariation_nonneg (f : ℝ → ℂ) (a b : ℝ) :
    0 ≤ rootWeightVariation f a b :=
  add_nonneg (norm_nonneg _) (integral_nonneg (fun _ => norm_nonneg _))

theorem root_weight_indicator_integral (f : ℝ → ℂ)
    (hf : Differentiable ℝ f) (hdf : Continuous (deriv f))
    {a b y : ℝ} (hy : y ∈ Set.Icc a b) :
    (∫ t in a..b, if t ≤ y then deriv f t else 0) = f y-f a := by
  have heq : (fun t : ℝ => if t ≤ y then deriv f t else 0) =
      Set.indicator {t : ℝ | t ≤ y} (deriv f) := rfl
  rw [heq, intervalIntegral.integral_indicator hy]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => (hf t).hasDerivAt) (hdf.intervalIntegrable a y)

theorem root_weight_linear_integral (f : ℝ → ℂ)
    (hf : Differentiable ℝ f) (hdf : Continuous (deriv f)) (a b : ℝ) :
    (∫ t in a..b, deriv f t * ((b-t : ℝ) : ℂ)) =
      (∫ t in a..b, f t) - ((b-a : ℝ) : ℂ)*f a := by
  have hu (t : ℝ) : HasDerivAt (fun s : ℝ => ((b-s : ℝ) : ℂ)) (-1) t := by
    convert Complex.ofRealCLM.hasDerivAt.scomp t ((hasDerivAt_const t b).sub (hasDerivAt_id t)) using 1
    · ext s
      simp
    · norm_num
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := fun t : ℝ => ((b-t : ℝ) : ℂ)) (u' := fun _ => (-1 : ℂ))
    (v := f) (v' := deriv f)
    ((Complex.continuous_ofReal.comp (continuous_const.sub continuous_id)).continuousOn)
    hf.continuous.continuousOn (fun t _ => hu t) (fun t _ => (hf t).hasDerivAt)
    intervalIntegrable_const (hdf.intervalIntegrable a b)
  simp only [sub_self, Complex.ofReal_zero, zero_mul, zero_sub, neg_one_mul,
    intervalIntegral.integral_neg] at h
  have hcomm : (∫ t in a..b, ((b-t : ℝ) : ℂ) * deriv f t) =
      ∫ t in a..b, deriv f t * ((b-t : ℝ) : ℂ) := by
    apply intervalIntegral.integral_congr
    intro t _
    ring
  rw [hcomm] at h
  linear_combination h

/-- Finite Abel summation for arbitrary real atom positions, with no
rounding of the coordinates and with the left boundary term retained. -/
theorem root_weight_finite_abel {ι : Type*} (S : Finset ι) (x : ι → ℝ)
    (w : ι → ℂ) (f : ℝ → ℂ) {a b : ℝ} (hab : a ≤ b)
    (hx : ∀ i ∈ S, x i ∈ Set.Icc a b)
    (hf : Differentiable ℝ f) (hdf : Continuous (deriv f)) :
    (∑ i ∈ S, w i*f (x i)) = f a*(∑ i ∈ S, w i) +
      ∫ t in a..b, deriv f t * (∑ i ∈ S, if t ≤ x i then w i else 0) := by
  classical
  have hi (i : ι) : IntervalIntegrable
      (fun t : ℝ => if t ≤ x i then deriv f t*w i else 0) volume a b := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
    have hh := ((hdf.mul (continuous_const : Continuous (fun _ : ℝ => w i))).intervalIntegrable
      (μ := volume) a b).1.indicator
      (t := Set.Iic (x i)) measurableSet_Iic
    convert hh using 1
    ext t
    simp only [Set.indicator_apply, Set.mem_Iic, Pi.mul_apply]
  have hint : (∫ t in a..b, deriv f t * (∑ i ∈ S, if t ≤ x i then w i else 0)) =
      ∑ i ∈ S, (f (x i)-f a)*w i := by
    simp_rw [Finset.mul_sum, mul_ite, mul_zero]
    rw [intervalIntegral.integral_finsetSum (fun i _ => hi i)]
    apply Finset.sum_congr rfl
    intro i hiS
    have hfun : (fun t : ℝ => if t ≤ x i then deriv f t*w i else 0) =
        (fun t : ℝ => (if t ≤ x i then deriv f t else 0)*w i) := by
      funext t
      split_ifs <;> simp
    rw [hfun, intervalIntegral.integral_mul_const,
      root_weight_indicator_integral f hf hdf (hx i hiS)]
  rw [hint]
  simp_rw [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hs : (∑ i ∈ S, f (x i)*w i) = ∑ i ∈ S, w i*f (x i) := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hs]
  ring

theorem root_weight_tail_integrable {ι : Type*} (S : Finset ι) (x : ι → ℝ)
    (w : ι → ℂ) (f : ℝ → ℂ) {a b : ℝ} (hab : a ≤ b)
    (hdf : Continuous (deriv f)) :
    IntervalIntegrable (fun t => deriv f t * (∑ i ∈ S, if t ≤ x i then w i else 0))
      volume a b := by
  classical
  have hi (i : ι) : IntervalIntegrable
      (fun t : ℝ => if t ≤ x i then deriv f t*w i else 0) volume a b := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
    have hh := ((hdf.mul (continuous_const : Continuous (fun _ : ℝ => w i))).intervalIntegrable
      (μ := volume) a b).1.indicator (t := Set.Iic (x i)) measurableSet_Iic
    convert hh using 1
    ext t
    simp only [Set.indicator_apply, Set.mem_Iic, Pi.mul_apply]
  convert IntervalIntegrable.sum S (fun i _ => hi i) using 1
  ext t
  simp only [Finset.sum_apply, Finset.mul_sum, mul_ite, mul_zero]

theorem root_weight_finite_error_identity {ι : Type*} (S : Finset ι) (x : ι → ℝ)
    (w : ι → ℂ) (f : ℝ → ℂ) (ρ : ℂ) {a b : ℝ} (hab : a ≤ b)
    (hx : ∀ i ∈ S, x i ∈ Set.Icc a b)
    (hf : Differentiable ℝ f) (hdf : Continuous (deriv f)) :
    (∑ i ∈ S, w i*f (x i)) - ρ*(∫ t in a..b, f t) =
      f a*((∑ i ∈ S, w i) - ρ*((b-a : ℝ) : ℂ)) +
        ∫ t in a..b, deriv f t *
          ((∑ i ∈ S, if t ≤ x i then w i else 0) - ρ*((b-t : ℝ) : ℂ)) := by
  classical
  have htail := root_weight_tail_integrable S x w f hab hdf
  have hlin : IntervalIntegrable (fun t => deriv f t * (ρ*((b-t : ℝ) : ℂ))) volume a b :=
    (hdf.mul (continuous_const.mul (Complex.continuous_ofReal.comp
      (continuous_const.sub continuous_id)))).intervalIntegrable a b
  have heq : (∫ t in a..b, deriv f t *
      ((∑ i ∈ S, if t ≤ x i then w i else 0) - ρ*((b-t : ℝ) : ℂ))) =
      (∫ t in a..b, deriv f t * (∑ i ∈ S, if t ≤ x i then w i else 0)) -
        ρ*(∫ t in a..b, deriv f t*((b-t : ℝ) : ℂ)) := by
    simp_rw [mul_sub]
    rw [intervalIntegral.integral_sub htail hlin]
    congr 1
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    ring
  rw [heq, root_weight_finite_abel S x w f hab hx hf hdf,
    root_weight_linear_integral f hf hdf]
  ring

/-- One-dimensional variation estimate, including the lower endpoint.
Only the actual tail-count discrepancy is used. -/
theorem root_weight_finite_error {ι : Type*} (S : Finset ι) (x : ι → ℝ)
    (w : ι → ℂ) (f : ℝ → ℂ) (ρ : ℂ) {a b E : ℝ} (hab : a ≤ b)
    (hx : ∀ i ∈ S, x i ∈ Set.Icc a b)
    (hf : Differentiable ℝ f) (hdf : Continuous (deriv f))
    (htail : ∀ t ∈ Set.Icc a b,
      ‖(∑ i ∈ S, if t ≤ x i then w i else 0) - ρ*((b-t : ℝ) : ℂ)‖ ≤ E) :
    ‖(∑ i ∈ S, w i*f (x i)) - ρ*(∫ t in a..b, f t)‖ ≤
      E*rootWeightVariation f a b := by
  classical
  have hsum : (∑ i ∈ S, if a ≤ x i then w i else 0) = ∑ i ∈ S, w i := by
    apply Finset.sum_congr rfl
    intro i hi
    exact ite_eq_left (hx i hi).1
  have htotal := htail a ⟨le_rfl, hab⟩
  rw [hsum] at htotal
  have hdom : IntegrableOn (fun t => E*‖deriv f t‖) (Set.Ioc a b) :=
    (continuous_const.mul hdf.norm).continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hint : ‖∫ t in a..b, deriv f t *
      ((∑ i ∈ S, if t ≤ x i then w i else 0) - ρ*((b-t : ℝ) : ℂ))‖ ≤
      E*(∫ t in Set.Ioc a b, ‖deriv f t‖) := by
    rw [intervalIntegral.integral_of_le hab]
    have hi := norm_integral_le_of_norm_le
      (f := fun t => deriv f t *
        ((∑ i ∈ S, if t ≤ x i then w i else 0) - ρ*((b-t : ℝ) : ℂ))) hdom (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left (htail t ⟨ht.1.le, ht.2⟩) (norm_nonneg _)).trans_eq
        (mul_comm _ _))
    simpa only [integral_const_mul] using hi
  rw [root_weight_finite_error_identity S x w f ρ hab hx hf hdf]
  calc
    _ ≤ ‖f a*((∑ i ∈ S, w i) - ρ*((b-a : ℝ) : ℂ))‖ +
        ‖∫ t in a..b, deriv f t *
          ((∑ i ∈ S, if t ≤ x i then w i else 0) - ρ*((b-t : ℝ) : ℂ))‖ := norm_add_le _ _
    _ ≤ ‖f a‖*E + E*(∫ t in Set.Ioc a b, ‖deriv f t‖) :=
      add_le_add (by rw [norm_mul]; exact mul_le_mul_of_nonneg_left htotal (norm_nonneg _)) hint
    _ = _ := by unfold rootWeightVariation; ring

/-- Two Abel steps preserve the rectangle discrepancy, multiplied only by
the product of the two one-dimensional variation norms. -/
theorem root_weight_rectangle_error {ι : Type*} (S : Finset ι) (x y : ι → ℝ)
    (w : ι → ℂ) (f g : ℝ → ℂ) (ρ : ℂ) {a b c d E : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d)
    (hx : ∀ i ∈ S, x i ∈ Set.Icc a b) (hy : ∀ i ∈ S, y i ∈ Set.Icc c d)
    (hf : Differentiable ℝ f) (hdf : Continuous (deriv f))
    (hg : Differentiable ℝ g) (hdg : Continuous (deriv g))
    (hrect : ∀ t ∈ Set.Icc a b, ∀ s ∈ Set.Icc c d,
      ‖(∑ i ∈ S, if t ≤ x i ∧ s ≤ y i then w i else 0) -
        ρ*((b-t : ℝ) : ℂ)*((d-s : ℝ) : ℂ)‖ ≤ E) :
    ‖(∑ i ∈ S, w i*f (x i)*g (y i)) -
      ρ*(∫ t in a..b, f t)*(∫ s in c..d, g s)‖ ≤
        E*rootWeightVariation f a b*rootWeightVariation g c d := by
  classical
  have hprefix (s : ℝ) (hs : s ∈ Set.Icc c d) :
      ‖(∑ i ∈ S, if s ≤ y i then w i*f (x i) else 0) -
        (ρ*(∫ t in a..b, f t))*((d-s : ℝ) : ℂ)‖ ≤ E*rootWeightVariation f a b := by
    have hh := root_weight_finite_error S x
      (fun i => if s ≤ y i then w i else 0) f (ρ*((d-s : ℝ) : ℂ)) (E := E) hab hx hf hdf
      (fun t ht => ?_)
    · convert hh using 1
      · simp only [ite_mul, zero_mul]
        ring_nf
    · simpa only [← ite_and, mul_assoc, mul_comm, mul_left_comm] using hrect t ht s hs
  exact root_weight_finite_error S y (fun i => w i*f (x i)) g
    (ρ*(∫ t in a..b, f t)) hcd hy hg hdg hprefix

end ArtinMatthews
