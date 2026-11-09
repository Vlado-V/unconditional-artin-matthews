module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Tactic


set_option backward.privateInPublic true
@[expose] public section

/-! A fixed power saving dominates the actual subexponential number of
sparse frequency samples, uniformly in every larger integer scale. -/

namespace ArtinMatthews

open Filter
open scoped Topology

/-- Uniform absorption of the off-diagonal power-saving error into the
main Gram row scale. `N` may be any real upper bound for the sample count. -/
theorem marked_sparse_power_error_absorption (C d η : ℝ)
    (hd : 0 < d) (hη : 0 < η) :
    ∀ᶠ L : ℝ in atTop, ∀ U N : ℝ,
      Real.exp (d*L) ≤ U → N ≤ Real.exp (C*L^(91/(100:ℝ))) →
      N * U^(1-η) ≤ U := by
  have hlim : Tendsto (fun L : ℝ => C * L^(-(9/(100:ℝ)))) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 9/100)).const_mul C
  filter_upwards [hlim.eventually (gt_mem_nhds (mul_pos hη hd)),
    eventually_gt_atTop (0:ℝ)] with L hsmall hL
  intro U N hU hN
  have hU0 : 0 < U := lt_of_lt_of_le (Real.exp_pos _) hU
  have hpower : L^(91/(100:ℝ)) = L^(-(9/(100:ℝ))) * L := by
    conv_lhs => rw [show (91/(100:ℝ)) = -(9/(100:ℝ)) + 1 by norm_num]
    rw [Real.rpow_add hL, Real.rpow_one]
  have hcost : C*L^(91/(100:ℝ)) ≤ η*(d*L) := by
    rw [hpower]
    nlinarith
  have hNpow : N ≤ U^η := by
    calc
      N ≤ Real.exp (C*L^(91/(100:ℝ))) := hN
      _ ≤ Real.exp (η*(d*L)) := Real.exp_le_exp.mpr hcost
      _ = (Real.exp (d*L))^η := by rw [mul_comm η, Real.exp_mul]
      _ ≤ U^η := Real.rpow_le_rpow (Real.exp_pos _).le hU hη.le
  calc
    _ ≤ U^η * U^(1-η) :=
      mul_le_mul_of_nonneg_right hNpow (Real.rpow_nonneg hU0.le _)
    _ = U := by rw [← Real.rpow_add hU0]; ring_nf; rw [Real.rpow_one]

/-- A fixed multiplicative factor in the interval count is harmless. -/
theorem marked_sparse_power_error_absorption_mul (K C d η : ℝ)
    (hd : 0 < d) (hη : 0 < η) :
    ∀ᶠ L : ℝ in atTop, ∀ U N : ℝ,
      Real.exp (d*L) ≤ U → N ≤ K*Real.exp (C*L^(91/(100:ℝ))) →
      N * U^(1-η) ≤ U := by
  have hscale : Tendsto (fun L : ℝ => Real.exp (L^(91/(100:ℝ)))) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_rpow_atTop (by norm_num))
  filter_upwards [marked_sparse_power_error_absorption (C+1) d η hd hη,
    hscale.eventually (eventually_ge_atTop K)] with L hbound hK
  intro U N hU hN
  apply hbound U N hU
  calc
    N ≤ K*Real.exp (C*L^(91/(100:ℝ))) := hN
    _ ≤ Real.exp (L^(91/(100:ℝ)))*Real.exp (C*L^(91/(100:ℝ))) :=
      mul_le_mul_of_nonneg_right hK (Real.exp_pos _).le
    _ = Real.exp ((C+1)*L^(91/(100:ℝ))) := by rw [← Real.exp_add]; congr 1; ring

end ArtinMatthews
