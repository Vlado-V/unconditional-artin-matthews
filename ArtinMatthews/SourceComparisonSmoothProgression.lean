module

public import ArtinMatthews.MarkedProgressionSmooth
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar


set_option backward.privateInPublic true
@[expose] public section

/-! Smooth progression comparison with the complete complex residue average.
All errors use the unscaled total variation of the test. -/
namespace ArtinMatthews
open Finset MeasureTheory
open scoped BigOperators
noncomputable section

theorem sourceComparisonSmoothSum_error (c : ℕ → ℂ) (f : ℝ → ℂ)
    {T E : ℝ} (ρ : ℂ) (hT : 0 ≤ T) (hf : Differentiable ℝ f)
    (hderiv : Continuous (deriv f)) (hfT : f T = 0)
    (hprefix : ∀ t ∈ Set.Ioc 0 T,
      ‖(∑ k ∈ Icc 0 ⌊t⌋₊, c k) - ρ * (t : ℂ)‖ ≤ E) :
    ‖(∑ k ∈ Icc 0 ⌊T⌋₊, f k * c k) - ρ * ∫ t in Set.Ioc 0 T, f t‖ ≤
      E * ∫ t in Set.Ioc 0 T, ‖deriv f t‖ := by
  have hfi : IntegrableOn (deriv f) (Set.Icc 0 T) := hderiv.continuousOn.integrableOn_Icc
  have hab := sum_mul_eq_sub_integral_mul c hT (fun t _ => hf t) hfi
  rw [hfT, zero_mul, zero_sub] at hab
  have hc (t : ℝ) : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 t := by
    simpa using (hasDerivAt_id t).ofReal_comp
  have hp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun t : ℝ => (t : ℂ)) (u' := fun _ => (1 : ℂ)) (v := f) (v' := deriv f)
    (a := 0) (b := T) (fun t _ => hc t) (fun t _ => (hf t).hasDerivAt)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℂ)) volume 0 T)
    (hderiv.intervalIntegrable 0 T)
  simp only [hfT, Complex.ofReal_zero, mul_zero, zero_mul, sub_zero, one_mul, zero_sub] at hp
  rw [intervalIntegral.integral_of_le hT, intervalIntegral.integral_of_le hT] at hp
  have hmain : (∫ t in Set.Ioc 0 T, deriv f t * (t : ℂ)) = -(∫ t in Set.Ioc 0 T, f t) := by
    simpa only [mul_comm] using hp
  have hA : IntegrableOn (fun t => deriv f t * ∑ k ∈ Icc 0 ⌊t⌋₊, c k)
      (Set.Ioc 0 T) :=
    (integrableOn_mul_sum_Icc c (a := 0) (b := T) (m := 0) le_rfl hfi).mono_set
      Set.Ioc_subset_Icc_self
  have ht : IntegrableOn (fun t : ℝ => deriv f t * (t : ℂ)) (Set.Ioc 0 T) :=
    (hderiv.mul Complex.continuous_ofReal).continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have herror : (∑ k ∈ Icc 0 ⌊T⌋₊, f k * c k) - ρ * ∫ t in Set.Ioc 0 T, f t =
      -(∫ t in Set.Ioc 0 T, deriv f t * ((∑ k ∈ Icc 0 ⌊t⌋₊, c k) - ρ * (t : ℂ))) := by
    rw [hab]
    simp_rw [mul_sub, show ∀ t : ℝ, deriv f t * (ρ * (t : ℂ)) = ρ * (deriv f t * (t : ℂ)) by
      intro t
      ring]
    rw [integral_sub hA (ht.const_mul ρ), integral_const_mul, hmain]
    ring
  rw [herror, norm_neg]
  have hbound : IntegrableOn (fun t => E * ‖deriv f t‖) (Set.Ioc 0 T) :=
    (continuous_const.mul hderiv.norm).continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hi := norm_integral_le_of_norm_le
    (f := fun t => deriv f t * ((∑ k ∈ Icc 0 ⌊t⌋₊, c k) - ρ * (t : ℂ))) hbound (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left (hprefix t ht) (norm_nonneg _)).trans_eq (mul_comm _ _))
  simpa only [integral_const_mul] using hi

def sourceComparisonResidueMean (k : ℕ) [NeZero k] (A : ZMod k → ℂ) : ℂ :=
  (∑ a, A a) / (k : ℂ)

private theorem comparisonResiduePrefix (d k : ℕ) [NeZero k]
    (hd : 0 < d) (hcop : d.Coprime k) (a : ZMod k) {u : ℝ} (hu : 0 ≤ u) :
    |(∑ n ∈ Icc 0 ⌊u⌋₊, if d ∣ n ∧ (n : ZMod k) = a then (1 : ℝ) else 0) -
      u / (d * k : ℕ)| ≤ 3 := by
  classical
  let r := Nat.chineseRemainder hcop 0 a.val
  have he (n : ℕ) : (n : ZMod k) = a ↔ Nat.ModEq k n a.val := by
    simpa only [ZMod.natCast_zmod_val] using ZMod.natCast_eq_natCast_iff n a.val k
  have hclass (n : ℕ) : d ∣ n ∧ (n : ZMod k) = a ↔ Nat.ModEq (d * k) n r.val := by
    rw [he]
    constructor
    · rintro ⟨hn, ha⟩
      exact Nat.chineseRemainder_modEq_unique hcop (Nat.modEq_zero_iff_dvd.mpr hn) ha
    · intro hn
      have hh := (Nat.modEq_and_modEq_iff_modEq_mul hcop).mpr hn
      exact ⟨Nat.modEq_zero_iff_dvd.mp (hh.1.trans r.property.1), hh.2.trans r.property.2⟩
  simpa only [hclass] using marked_residue_prefix_error (d * k) r.val
    (Nat.mul_pos hd (NeZero.pos k)) hu

theorem sourceComparisonPeriodicPrefix_error (d k : ℕ) [NeZero k]
    (hd : 0 < d) (hcop : d.Coprime k) (A : ZMod k → ℂ) (hA : ∀ a, ‖A a‖ ≤ 1)
    {u : ℝ} (hu : 0 ≤ u) :
    ‖(∑ n ∈ Icc 0 ⌊u⌋₊, if d ∣ n then A (n : ZMod k) else 0) -
      (sourceComparisonResidueMean k A / (d : ℂ)) * (u : ℂ)‖ ≤ 3 * (k : ℝ) := by
  classical
  let c (a : ZMod k) (n : ℕ) : ℝ := if d ∣ n ∧ (n : ZMod k) = a then 1 else 0
  have hc (n : ℕ) : (if d ∣ n then A (n : ZMod k) else 0) =
      ∑ a : ZMod k, A a * (c a n : ℂ) := by
    by_cases hn : d ∣ n
    · rw [ite_eq_left hn]
      symm
      rw [sum_eq_single (n : ZMod k)]
      · simp [c, hn]
      · intro a _ ha
        simp [c, hn, Ne.symm ha]
      · simp
    · simp [c, hn]
  have hs :
      (∑ n ∈ Icc 0 ⌊u⌋₊, if d ∣ n then A (n : ZMod k) else 0) =
        ∑ a : ZMod k, A a * ((∑ n ∈ Icc 0 ⌊u⌋₊, c a n : ℝ) : ℂ) := by
    simp_rw [hc]
    rw [sum_comm]
    simp only [Complex.ofReal_sum, mul_sum]
  have hmain : (sourceComparisonResidueMean k A / (d : ℂ)) * (u : ℂ) =
      ∑ a : ZMod k, A a * ((u / (d * k : ℕ) : ℝ) : ℂ) := by
    unfold sourceComparisonResidueMean
    rw [← sum_mul]
    change _ = (∑ a, A a) * ((u / ((d * k : ℕ) : ℝ) : ℝ) : ℂ)
    rw [Complex.ofReal_div, Complex.ofReal_natCast, Nat.cast_mul]
    ring
  rw [hs, hmain, ← sum_sub_distrib]
  calc
    _ ≤ ∑ a : ZMod k, ‖A a * (((∑ n ∈ Icc 0 ⌊u⌋₊, c a n : ℝ) : ℂ) -
        ((u / (d * k : ℕ) : ℝ) : ℂ))‖ := by simp only [← mul_sub]; exact norm_sum_le _ _
    _ ≤ ∑ _a : ZMod k, (3 : ℝ) := by
      apply sum_le_sum
      intro a _
      rw [← Complex.ofReal_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      simpa only [one_mul] using mul_le_mul (hA a)
        (comparisonResiduePrefix d k hd hcop a hu) (abs_nonneg _) zero_le_one
    _ = _ := by simp [ZMod.card, mul_comm]

theorem sourceComparisonDivisorSmoothPhase_error (d k : ℕ) [NeZero k]
    (hd : 0 < d) (hcop : d.Coprime k) (A : ZMod k → ℂ) (hA : ∀ a, ‖A a‖ ≤ 1)
    (f : ℝ → ℂ) {T : ℝ} (hT : 0 ≤ T) (hf : Differentiable ℝ f)
    (hderiv : Continuous (deriv f)) (hfT : f T = 0) :
    ‖(∑ n ∈ Icc 0 ⌊T⌋₊, if d ∣ n then A (n : ZMod k) * f n else 0) -
      (sourceComparisonResidueMean k A / (d : ℂ)) * ∫ t in Set.Ioc 0 T, f t‖ ≤
      (3 * (k : ℝ)) * ∫ t in Set.Ioc 0 T, ‖deriv f t‖ := by
  have h := sourceComparisonSmoothSum_error (fun n => if d ∣ n then A (n : ZMod k) else 0)
    f (sourceComparisonResidueMean k A / (d : ℂ)) hT hf hderiv hfT
      (fun u hu => sourceComparisonPeriodicPrefix_error d k hd hcop A hA hu.1.le)
  have he (n : ℕ) : f n * (if d ∣ n then A (n : ZMod k) else 0) =
      if d ∣ n then A (n : ZMod k) * f n else 0 := by
    split_ifs <;> simp [mul_comm]
  simpa only [he] using h

def sourceComparisonRationalPhase (k : ℕ) [NeZero k] (h : ℤ) (a : ZMod k) : ℂ :=
  ZMod.stdAddChar ((h : ZMod k) * a)

theorem sourceComparisonRationalPhase_norm (k : ℕ) [NeZero k] (h : ℤ) (a : ZMod k) :
    ‖sourceComparisonRationalPhase k h a‖ = 1 := by
  rw [sourceComparisonRationalPhase, ZMod.stdAddChar_apply]
  exact Circle.norm_coe _

theorem sourceComparisonRationalPhase_nat (k : ℕ) [NeZero k] (h : ℤ) (n : ℕ) :
    sourceComparisonRationalPhase k h (n : ZMod k) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (h : ℂ) * (n : ℂ) / (k : ℂ)) := by
  have he : ((h * (n : ℤ) : ℤ) : ZMod k) = (h : ZMod k) * (n : ZMod k) := by push_cast; rfl
  rw [sourceComparisonRationalPhase, ← he, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  ring

end
end ArtinMatthews
