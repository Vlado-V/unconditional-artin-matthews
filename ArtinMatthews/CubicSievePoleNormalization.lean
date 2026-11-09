module

public import ArtinMatthews.CubicSievePoleIntegralBound


set_option backward.privateInPublic true
@[expose] public section

/-! Exact normalization of the value, derivative, and retained errors. -/

noncomputable section
namespace ArtinMatthews

theorem cubicSieve_pole_normalized_envelope {x L W γ C E J J' : ℝ}
    (hx : 0 < x) (hL : 1 ≤ L) (hW : 0 < W) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hC : 0 ≤ C) (hE : 0 ≤ E)
    (hJ : |J| ≤ W * C * E / (γ ^ 2 * L ^ 2) + 1 / L ^ 3)
    (hJ' : |J'| ≤ W * C * E / (γ * L) + 1 / L ^ 3) :
    L / (x * W) * (2 * x * (2 * L * |J| + |J'|) + 2 * x / L ^ 2) ≤
      6 * C * E / γ ^ 2 + 8 / (W * L) := by
  have hL₀ : 0 < L := zero_lt_one.trans_le hL
  have hγsq : γ ^ 2 ≤ γ := by nlinarith only [hγ1, hγ]
  have hγterm : 2 * C * E / γ ≤ 2 * C * E / γ ^ 2 :=
    div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hγ) hγsq
  have hLsq : L ≤ L ^ 2 := by nlinarith only [hL]
  have hLterm : 2 / (W * L ^ 2) ≤ 2 / (W * L) :=
    div_le_div_of_nonneg_left (by norm_num) (mul_pos hW hL₀)
      (mul_le_mul_of_nonneg_left hLsq hW.le)
  calc
    _ ≤ L / (x * W) * (2 * x *
        (2 * L * (W * C * E / (γ ^ 2 * L ^ 2) + 1 / L ^ 3) +
          (W * C * E / (γ * L) + 1 / L ^ 3)) + 2 * x / L ^ 2) := by
      gcongr
    _ = 4 * C * E / γ ^ 2 + 2 * C * E / γ + 6 / (W * L) + 2 / (W * L ^ 2) := by
      field_simp
      ring
    _ ≤ 4 * C * E / γ ^ 2 + 2 * C * E / γ ^ 2 + 6 / (W * L) + 2 / (W * L) :=
      add_le_add (add_le_add (add_le_add le_rfl hγterm) le_rfl) hLterm
    _ = _ := by ring

end ArtinMatthews
