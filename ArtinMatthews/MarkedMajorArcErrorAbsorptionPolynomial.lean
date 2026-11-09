module

public import ArtinMatthews.MarkedMajorArcErrorAbsorptionBounds


set_option backward.privateInPublic true
@[expose] public section

/-! A polynomial-times-exponential majorant for the literal contour error. -/
namespace ArtinMatthews
open Filter
open scoped Topology

noncomputable def markedMajorRieszPolynomial (K C η τ L H : ℝ) : ℝ :=
  2 * (C + 1) * Real.exp η * L / H +
    4 * K * H * L^3 * Real.exp (-τ * L^(1/4 : ℝ)) +
    4 * K * Real.exp η * L^2 / H^2

theorem marked_major_riesz_envelope_le_polynomial {K C η τ L H : ℝ}
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hL : 1 ≤ L) (hH : 0 < H)
    (hδ : L^(-(3/4 : ℝ)) ≤ 1/2) :
    markedMajorRieszEnvelope K C η τ L H ≤ markedMajorRieszPolynomial K C η τ L H := by
  have hLp : 0 < L := by linarith
  let δ := L^(-(3/4 : ℝ))
  have hδp : 0 < δ := Real.rpow_pos_of_pos hLp _
  have hδhalf : δ ≤ 1/2 := hδ
  have hden : 0 < δ * (1-δ) := mul_pos hδp (by linarith)
  have hLd : 1 ≤ L * δ := by
    have he : L * δ = L^(1/4 : ℝ) := by
      change L * L^(-(3/4 : ℝ)) = _
      calc
        _ = L^(1 : ℝ) * L^(-(3/4 : ℝ)) := by rw [Real.rpow_one]
        _ = L^((1 : ℝ) + -(3/4 : ℝ)) := (Real.rpow_add hLp _ _).symm
        _ = _ := by norm_num
    rw [he]
    exact Real.one_le_rpow hL (by norm_num)
  have hinv : (δ * (1-δ))⁻¹ ≤ 2 * L := by
    rw [inv_eq_one_div, div_le_iff₀ hden]
    have hh := mul_le_mul hLd (show (1/2 : ℝ) ≤ 1-δ by linarith)
      (by norm_num : (0 : ℝ) ≤ 1/2) (by positivity : 0 ≤ L*δ)
    nlinarith
  have hCL : C + L ≤ (C + 1) * L := by nlinarith
  have hsum : 1/L + δ ≤ 2 := by
    have hh : 1/L ≤ 1 := (div_le_one hLp).mpr hL
    linarith
  have hnum : 0 ≤
      2*(C+L)*Real.exp η/H +
      2*H*(K*L^2*Real.exp (-τ*L^(1/4 : ℝ))/(δ*(1-δ))) +
      2*(K*L^2*Real.exp η/H^2)*(1/L+δ) := by positivity
  have hfirst : 2*(C+L)*Real.exp η/H ≤ 2*(C+1)*Real.exp η*L/H := by
    calc
      _ ≤ 2*((C+1)*L)*Real.exp η/H := by gcongr
      _ = _ := by ring
  have hsecond : 2*H*(K*L^2*Real.exp (-τ*L^(1/4 : ℝ))/(δ*(1-δ))) ≤
      4*K*H*L^3*Real.exp (-τ*L^(1/4 : ℝ)) := by
    calc
      _ = 2*H*(K*L^2*Real.exp (-τ*L^(1/4 : ℝ))*(δ*(1-δ))⁻¹) := by rw [div_eq_mul_inv]
      _ ≤ 2*H*(K*L^2*Real.exp (-τ*L^(1/4 : ℝ))*(2*L)) := by gcongr
      _ = _ := by ring
  have hthird : 2*(K*L^2*Real.exp η/H^2)*(1/L+δ) ≤
      4*K*Real.exp η*L^2/H^2 := by
    calc
      _ ≤ 2*(K*L^2*Real.exp η/H^2)*2 := by gcongr
      _ = _ := by ring
  have hpi : 1 ≤ 2*Real.pi := by linarith [Real.pi_gt_three]
  exact (div_le_self hnum hpi).trans (add_le_add (add_le_add hfirst hsecond) hthird)

end ArtinMatthews
