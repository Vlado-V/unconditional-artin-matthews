module

public import ArtinMatthews.MarkedMajorArcProductBudget


set_option backward.privateInPublic true
@[expose] public section

/-! The actual product-mean envelope uniformly for all interval lengths. -/
namespace ArtinMatthews
open Filter
open scoped Topology

 theorem marked_product_mean_envelope_uniform_all_lengths (σ D : ℝ)
    (hσ : 0 ≤ σ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ L : ℝ in atTop, ∀ H U T : ℝ,
      0 < H → 0 < U → 1 ≤ H*U → 0 ≤ T → H*U ≤ Real.exp (σ*L) →
      markedProductMeanEnvelope H U T
        (1+(markedSieveEulerProduct (Real.exp (L^(6/25:ℝ))))⁻¹) (L^D) ≤
          C*L^(2*D+5)*(1+T/(H*U)) := by
  let E := Real.exp (Real.eulerMascheroniConstant+1)
  let J := 1+Real.log 4+σ
  have hE : 0 < E := Real.exp_pos _
  have hJ : 0 < J := by dsimp [J]; have := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4); linarith
  refine ⟨128*Real.exp 1*(1+E)^2*J^3,by positivity,?_⟩
  filter_upwards [marked_rough_density_inverse_cutoff (6/25) (by norm_num),
    eventually_ge_atTop (1:ℝ)] with L hV hL
  have hLp : 0 < L := zero_lt_one.trans_le hL
  intro H U T hH hU hX hT hupper
  have hV0 := markedSieveEulerProduct_pos (Real.exp (L^(6/25:ℝ)))
  have hA : 1+(markedSieveEulerProduct (Real.exp (L^(6/25:ℝ))))⁻¹ ≤ (1+E)*L := by
    have hp : L^(6/25:ℝ) ≤ L := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hL (by norm_num : (6/25:ℝ) ≤ 1)
    have hh := mul_le_mul_of_nonneg_left hp hE.le
    change (markedSieveEulerProduct (Real.exp (L^(6/25:ℝ))))⁻¹ ≤ E*L^(6/25:ℝ) at hV
    nlinarith
  have hlog : 1+Real.log (4*H*U) ≤ J*L := by
    have hh : Real.log (H*U) ≤ σ*L := (Real.log_le_iff_le_exp (mul_pos hH hU)).mpr hupper
    rw [show 4*H*U=4*(H*U) by ring,Real.log_mul (by norm_num) (mul_pos hH hU).ne']
    dsimp [J]
    nlinarith [Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4)]
  have hlog0 : 0 ≤ 1+Real.log (4*H*U) := by
    have hh : 1 ≤ 4*H*U := by nlinarith
    have := Real.log_nonneg hh
    linarith
  calc
    _ ≤ 128*Real.exp 1*(1+T/(H*U))*
        (1+(markedSieveEulerProduct (Real.exp (L^(6/25:ℝ))))⁻¹)^2*(L^D)^2*
          (1+Real.log (4*H*U))^3 := marked_product_mean_envelope_bound H U T _ _ hH hU hX hT
    _ ≤ 128*Real.exp 1*(1+T/(H*U))*((1+E)*L)^2*(L^D)^2*(J*L)^3 := by
      gcongr
    _ = (128*Real.exp 1*(1+E)^2*J^3)*L^(2*D+5)*(1+T/(H*U)) := by
      rw [Real.rpow_add hLp,show 2*D=D*2 by ring,Real.rpow_mul hLp.le,Real.rpow_two,
        show (5:ℝ)=(5:ℕ) by norm_num,Real.rpow_natCast]
      ring

end ArtinMatthews
