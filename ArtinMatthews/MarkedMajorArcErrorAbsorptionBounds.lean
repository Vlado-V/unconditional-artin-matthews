module

public import ArtinMatthews.MarkedMajorArcInterval
public import ArtinMatthews.MarkedBonferroniTail


set_option backward.privateInPublic true
@[expose] public section

/-! Uniform numerical bounds for the actual contour errors in the marked
major arcs. No cancellation estimate is assumed here. -/
namespace ArtinMatthews
open Filter
open scoped Topology

theorem marked_major_positive_power_bound {η L x : ℝ}
    (hL : 0 < L) (hx : 0 < x) (hhi : x ≤ Real.exp (η * L)) :
    x ^ (1 / L) ≤ Real.exp η := by
  have h := Real.rpow_le_rpow hx.le hhi (show 0 ≤ 1 / L by positivity)
  rw [← Real.exp_mul] at h
  convert h using 1
  congr 1
  field_simp

theorem marked_major_negative_power_bound {τ L x : ℝ}
    (hL : 0 < L) (hlo : Real.exp (τ * L) ≤ x) :
    x ^ (-L ^ (-(3 / 4 : ℝ))) ≤ Real.exp (-τ * L ^ (1 / 4 : ℝ)) := by
  have h := Real.rpow_le_rpow_of_nonpos (Real.exp_pos _) hlo
    (neg_nonpos.mpr (Real.rpow_nonneg hL.le (-(3 / 4 : ℝ))))
  rw [← Real.exp_mul] at h
  have hid : L * L ^ (-(3 / 4 : ℝ)) = L ^ (1 / 4 : ℝ) := by
    calc
      _ = L ^ (1 : ℝ) * L ^ (-(3 / 4 : ℝ)) := by rw [Real.rpow_one]
      _ = L ^ ((1 : ℝ) + -(3 / 4 : ℝ)) := (Real.rpow_add hL _ _).symm
      _ = _ := by norm_num
  convert h using 1
  congr 1
  rw [show τ * L * -L ^ (-(3 / 4 : ℝ)) =
    -τ * (L * L ^ (-(3 / 4 : ℝ))) by ring, hid]

noncomputable def markedMajorRieszEnvelope (K C η τ L H : ℝ) : ℝ :=
  (2 * (C + L) * Real.exp η / H +
    2 * H * (K * L^2 * Real.exp (-τ * L^(1/4 : ℝ)) /
      (L^(-(3/4 : ℝ)) * (1 - L^(-(3/4 : ℝ))))) +
    2 * (K * L^2 * Real.exp η / H^2) * (1/L + L^(-(3/4 : ℝ)))) /
    (2 * Real.pi)

theorem marked_major_riesz_error_le_envelope {K C η τ L H x : ℝ}
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hL : 0 < L) (hH : 0 < H)
    (hδ : L^(-(3/4 : ℝ)) < 1)
    (hlo : Real.exp (τ * L) ≤ x) (hhi : x ≤ Real.exp (η * L)) :
    markedMajorRieszError K C L H x ≤ markedMajorRieszEnvelope K C η τ L H := by
  have hx : 0 < x := (Real.exp_pos _).trans_le hlo
  have hpos := marked_major_positive_power_bound hL hx hhi
  have hneg := marked_major_negative_power_bound hL hlo
  have hden : 0 < L^(-(3/4 : ℝ)) * (1 - L^(-(3/4 : ℝ))) :=
    mul_pos (Real.rpow_pos_of_pos hL _) (sub_pos.mpr hδ)
  unfold markedMajorRieszError markedMajorRieszEnvelope
  gcongr

end ArtinMatthews
