module

public import ArtinMatthews.MarkedMajorArcErrorAbsorptionPolynomial


set_option backward.privateInPublic true
@[expose] public section

/-! The explicit Riesz error saves any prescribed logarithmic power with a
fixed polynomial contour height. -/
namespace ArtinMatthews
open Filter
open scoped Topology

theorem marked_major_riesz_polynomial_tendsto (K C η τ p B : ℝ)
    (hτ : 0 < τ) (hp : 0 ≤ p) (hB : p + 5 < B) :
    Tendsto (fun L : ℝ => L^p * markedMajorRieszPolynomial K C η τ L (L^B))
      atTop (𝓝 0) := by
  have h₁ := (tendsto_rpow_neg_atTop (show 0 < B-p-1 by linarith)).const_mul
    (2*(C+1)*Real.exp η)
  have h₂ := (rpow_mul_exp_neg_rpow_tendsto (p+B+3)
    (by norm_num : (0 : ℝ) < 1/4) hτ).const_mul (4*K)
  have h₃ := (tendsto_rpow_neg_atTop (show 0 < 2*B-p-2 by linarith)).const_mul
    (4*K*Real.exp η)
  have hh := (h₁.add h₂).add h₃
  simp only [mul_zero, add_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  have he₁ : L^p * L / L^B = L^(p+1-B) := by
    calc
      _ = (L^p * L^(1 : ℝ)) / L^B := by rw [Real.rpow_one]
      _ = L^(p+1) / L^B := by rw [← Real.rpow_add hL]
      _ = _ := (Real.rpow_sub hL _ _).symm
  have he₂ : L^p * L^B * L^3 = L^(p+B+3) := by
    rw [← Real.rpow_natCast L 3, ← Real.rpow_add hL, ← Real.rpow_add hL]
    norm_num
  have hBsq : (L^B)^2 = L^(2*B) := by
    rw [← Real.rpow_mul_natCast hL.le]
    congr 1
    norm_num
    ring
  have he₃ : L^p * L^2 / (L^B)^2 = L^(p+2-2*B) := by
    rw [hBsq, ← Real.rpow_natCast L 2, ← Real.rpow_add hL]
    exact (Real.rpow_sub hL _ _).symm
  change 2*(C+1)*Real.exp η*L^(-(B-p-1)) +
      4*K*(L^(p+B+3)*Real.exp (-τ*L^(1/4 : ℝ))) +
      4*K*Real.exp η*L^(-(2*B-p-2)) = _
  rw [show -(B-p-1) = p+1-B by ring, show -(2*B-p-2) = p+2-2*B by ring,
    ← he₁, ← he₂, ← he₃]
  unfold markedMajorRieszPolynomial
  ring

theorem marked_major_riesz_uniform_power (K C η τ p B c : ℝ)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hτ : 0 < τ) (hp : 0 ≤ p)
    (hB : p+5 < B) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, ∀ x : ℝ,
      Real.exp (τ*L) ≤ x → x ≤ Real.exp (η*L) →
      markedMajorRieszError K C L (L^B) x ≤ c*L^(-p) := by
  have hs := (marked_major_riesz_polynomial_tendsto K C η τ p B hτ hp hB).eventually
    (Iio_mem_nhds hc)
  have hd := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3/4)).eventually
    (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1/2))
  filter_upwards [hs,hd,eventually_ge_atTop (1 : ℝ)] with L hs hd hL x hlo hhi
  have hLp : 0 < L := by linarith
  have hH : 0 < L^B := Real.rpow_pos_of_pos hLp _
  have he := (marked_major_riesz_error_le_envelope hK hC hLp hH
    (show L^(-(3/4 : ℝ)) < 1 by linarith) hlo hhi).trans
    (marked_major_riesz_envelope_le_polynomial hK hC hL hH hd.le)
  have hpow : 0 < L^p := Real.rpow_pos_of_pos hLp _
  apply (mul_le_mul_iff_of_pos_left hpow).mp
  have hid : L^p * L^(-p) = 1 := by rw [← Real.rpow_add hLp]; simp
  calc
    L^p * markedMajorRieszError K C L (L^B) x ≤
      L^p * markedMajorRieszPolynomial K C η τ L (L^B) :=
        mul_le_mul_of_nonneg_left he hpow.le
    _ ≤ c := hs.le
    _ = L^p * (c * L^(-p)) := by rw [mul_left_comm, hid, mul_one]

end ArtinMatthews
