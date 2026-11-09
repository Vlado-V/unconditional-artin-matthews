module

public import ArtinMatthews.CubicSieveDivisorLogProgression
public import ArtinMatthews.CubicSieveSmoothPrefix


set_option backward.privateInPublic true
@[expose] public section

/-! The exact shifted divisor progression against a smooth test. -/

noncomputable section
namespace ArtinMatthews

open Finset MeasureTheory
open scoped BigOperators

theorem cubicSieve_shiftedDivisorProgression_smooth_error {d r : ℕ} (hd : 0 < d)
    (hr : Squarefree r) (hc : d.Coprime r) (f : ℝ → ℝ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hlevel : (d : ℝ) ^ 2 * (r : ℝ) ^ 2 ≤ a)
    (hf : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t)
    (hdf : ContinuousOn (deriv f) (Set.Icc a b)) (hfa : f a = 0) (hfb : f b = 0) :
    |(∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, f n * cubicSieveShiftedDivisorCoefficient d r n) -
      ∫ t in Set.Ioc a b, f t * cubicSieveShiftedDivisorLogDensity d r t| ≤
      (34 * (2 : ℝ) ^ d.primeFactors.card * (3 : ℝ) ^ r.primeFactors.card *
        Real.sqrt (b / (r : ℝ))) * ∫ t in Set.Ioc a b, |deriv f t| := by
  refine cubicSieve_smooth_prefix_error (cubicSieveShiftedDivisorCoefficient d r) f
    (cubicSieveShiftedDivisorLogModel d r) (cubicSieveShiftedDivisorLogDensity d r)
    ha.le hab hf hdf hfa hfb ?_ ?_ ?_
  · exact fun t ht => cubicSieve_shiftedDivisorLogModel_hasDerivAt hd hr.ne_zero (ha.trans_le ht.1)
  · exact (cubicSieve_shiftedDivisorLogDensity_continuousOn hr.ne_zero).mono
      (fun _ ht => ha.trans_le ht.1)
  · intro t ht
    rw [cubicSieve_shiftedDivisorCoefficient_prefix]
    exact (cubicSieve_shiftedDivisorProgression_real_model_error hd hr hc
      (hlevel.trans ht.1.le)).trans
      (mul_le_mul_of_nonneg_left
        (Real.sqrt_le_sqrt (div_le_div_of_nonneg_right ht.2 (Nat.cast_nonneg r)))
        (by positivity))

end ArtinMatthews
