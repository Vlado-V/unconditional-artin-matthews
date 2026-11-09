module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic


set_option backward.privateInPublic true
@[expose] public section

/-! Exact cancellation of the denominator square against the Bessel square
scale, keeping the arbitrarily small coefficient exponent explicit. -/

namespace ArtinMatthews

theorem shiftedDualZero_scale (K q ε : ℝ) (hK : 0 < K) (hq : 0 < q) :
    K^2 * (q^2 / K)^(1 + ε) / q^2 = K^(1 - ε) * q^(2 * ε) := by
  have hKpow : K^(1 - ε) = K / K^ε := by
    rw [Real.rpow_sub hK, Real.rpow_one]
  have hqpow : (q^2)^ε = q^(2 * ε) := by
    rw [← Real.rpow_natCast q 2, ← Real.rpow_mul hq.le]
    norm_num
  rw [Real.div_rpow (sq_nonneg q) hK.le, Real.rpow_add (sq_pos_of_pos hq),
    Real.rpow_add hK, Real.rpow_one, Real.rpow_one, hqpow, hKpow]
  field_simp

end ArtinMatthews
