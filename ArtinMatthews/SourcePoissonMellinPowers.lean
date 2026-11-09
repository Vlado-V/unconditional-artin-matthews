module

public import ArtinMatthews.SourcePoissonTripleKernel
public import Mathlib.Analysis.SpecialFunctions.Pow.Real


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourcePhysical

theorem sourcePoissonRealPow_cpow {a : ℝ} (ha : 0 ≤ a) (n : ℕ) (s : ℂ) :
    ((a ^ n : ℝ) : ℂ) ^ s = (a : ℂ) ^ ((n : ℂ) * s) := by
  rw [Complex.ofReal_pow, ← Complex.cpow_nat_mul' (n := n)]
  · simp [Complex.arg_ofReal_of_nonneg ha, Real.pi_pos]
  · simp [Complex.arg_ofReal_of_nonneg ha, Real.pi_pos.le]

theorem sourcePoissonDiv_neg_cpow {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (s : ℂ) :
    ((a / b : ℝ) : ℂ) ^ (-s) = (a : ℂ) ^ (-s) * (b : ℂ) ^ s := by
  rw [Complex.ofReal_div, Complex.div_cpow_ofReal_nonneg ha hb, div_eq_mul_inv,
    Complex.cpow_neg (b : ℂ) s, inv_inv]

/-- The exact source powers after setting the Gaussian exponent to `ξ + z - 1`. -/
theorem sourcePoissonMellinPowers
    {X Y Z qc qn qs qr qu : ℝ} (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (hc : 0 < qc) (hn : 0 < qn) (hs : 0 < qs) (hr : 0 < qr) (hu : 0 < qu)
    (ξ w z : ℂ) :
    let A := qc * qn ^ 3
    let t := ξ + z - 1
    ((Real.sqrt X / (Y * Real.sqrt qc * qn * A) : ℝ) : ℂ) *
      ((A / Z : ℝ) : ℂ) ^ (-t) * ((qs / Y : ℝ) : ℂ) ^ (-w) *
      ((X * qu * qr ^ 6 / A : ℝ) : ℂ) ^ (-z) =
    (X : ℂ) ^ (1 / 2 - z) * (Z : ℂ) ^ t * (Y : ℂ) ^ (w - 1) *
      (qu : ℂ) ^ (-z) * (qc : ℂ) ^ (-1 / 2 - ξ) * (qn : ℂ) ^ (-1 - 3 * ξ) *
      (qs : ℂ) ^ (-w) * (qr : ℂ) ^ (-(6 * z)) := by
  let A := qc * qn ^ 3
  let t := ξ + z - 1
  change _ * ((A / Z : ℝ) : ℂ) ^ (-t) * _ * ((X * qu * qr ^ 6 / A : ℝ) : ℂ) ^ (-z) = _
  have hA : 0 < A := mul_pos hc (pow_pos hn _)
  have hhalf (a : ℝ) (ha : 0 ≤ a) : (Real.sqrt a : ℂ) = (a : ℂ) ^ (1 / 2 : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow ha]
    norm_num
  have hAp : (A : ℂ) ^ (-ξ) = (qc : ℂ) ^ (-ξ) * (qn : ℂ) ^ (-(3 * ξ)) := by
    dsimp [A]
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hc.le
      (pow_nonneg hn.le _), sourcePoissonRealPow_cpow hn.le]
    congr 1
    push_cast
    ring_nf
  have hAt : (A : ℂ) ^ (-1 : ℂ) * (A : ℂ) ^ (-t) * (A : ℂ) ^ z = (A : ℂ) ^ (-ξ) := by
    rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hA.ne'),
      ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hA.ne')]
    congr 1
    dsimp [t]
    ring_nf
  have hPref : ((Real.sqrt X / (Y * Real.sqrt qc * qn * A) : ℝ) : ℂ) =
      (X : ℂ) ^ (1 / 2 : ℂ) * ((Y : ℂ) ^ (-1 : ℂ) *
      (qc : ℂ) ^ (-(1 / 2) : ℂ) * (qn : ℂ) ^ (-1 : ℂ) * (A : ℂ) ^ (-1 : ℂ)) := by
    rw [Complex.ofReal_div]
    simp only [Complex.ofReal_mul, hhalf X hX.le, hhalf qc hc.le, div_eq_mul_inv,
      mul_inv, Complex.cpow_neg, Complex.cpow_one]
  rw [hPref, sourcePoissonDiv_neg_cpow hA.le hZ.le, sourcePoissonDiv_neg_cpow hs.le hY.le]
  have hz :
      ((X : ℂ) * (qu : ℂ) * (qr ^ 6 : ℝ) / (A : ℂ)) ^ (-z) =
        (X : ℂ) ^ (-z) * (qu : ℂ) ^ (-z) * (qr : ℂ) ^ (-(6 * z)) * (A : ℂ) ^ z := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_div,
      sourcePoissonDiv_neg_cpow (by positivity) hA.le, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (mul_nonneg hX.le hu.le) (pow_nonneg hr.le _),
      Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hX.le hu.le,
      sourcePoissonRealPow_cpow hr.le]
    congr 2
    push_cast
    ring_nf
  rw [show ((X * qu * qr ^ 6 / A : ℝ) : ℂ) =
      (X : ℂ) * (qu : ℂ) * (qr ^ 6 : ℝ) / (A : ℂ) by
        rw [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_mul], hz]
  have hpX := Complex.cpow_add (1 / 2) (-z) (Complex.ofReal_ne_zero.mpr hX.ne')
  have hpY := Complex.cpow_add w (-1) (Complex.ofReal_ne_zero.mpr hY.ne')
  have hpC := Complex.cpow_add (-(1 / 2)) (-ξ) (Complex.ofReal_ne_zero.mpr hc.ne')
  have hpN := Complex.cpow_add (-1) (-(3 * ξ)) (Complex.ofReal_ne_zero.mpr hn.ne')
  rw [show (1 / 2 - z : ℂ) = 1 / 2 + -z by ring,
    show (w - 1 : ℂ) = w + -1 by ring,
    show (-1 / 2 - ξ : ℂ) = -(1 / 2) + -ξ by ring,
    show (-1 - 3 * ξ : ℂ) = -1 + -(3 * ξ) by ring,
    hpX, hpY, hpC, hpN]
  calc
    _ = (X : ℂ) ^ (1 / 2 : ℂ) * (X : ℂ) ^ (-z) * (Z : ℂ) ^ t *
        (Y : ℂ) ^ w * (Y : ℂ) ^ (-1 : ℂ) * (qu : ℂ) ^ (-z) *
        (qc : ℂ) ^ (-(1 / 2) : ℂ) * (qn : ℂ) ^ (-1 : ℂ) *
        (qs : ℂ) ^ (-w) * (qr : ℂ) ^ (-(6 * z)) *
        ((A : ℂ) ^ (-1 : ℂ) * (A : ℂ) ^ (-t) * (A : ℂ) ^ z) := by ac_rfl
    _ = _ := by
      rw [hAt, hAp]
      dsimp [t]
      ac_rfl

end ArtinMatthews.SourcePhysical
