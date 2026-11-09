module

public import ArtinMatthews.MarkedMajorArcRoughMertens


set_option backward.privateInPublic true
@[expose] public section

/-! Explicit numerical bounds for the normalized product mean square. -/
namespace ArtinMatthews
open Filter
open scoped Topology

noncomputable def markedProductMeanEnvelope (H U T A B : ℝ) : ℝ :=
  8*Real.exp 1*(T+(⌊4*H*U⌋₊:ℝ))*
    (((A/H)*(B/U))^2*(⌊4*H*U⌋₊:ℝ)*(1+Real.log (⌊4*H*U⌋₊:ℝ))^3)

 theorem marked_product_mean_envelope_bound (H U T A B : ℝ)
    (hH : 0 < H) (hU : 0 < U) (hX : 1 ≤ H*U) (hT : 0 ≤ T) :
    markedProductMeanEnvelope H U T A B ≤
      128*Real.exp 1*(1+T/(H*U))*A^2*B^2*(1+Real.log (4*H*U))^3 := by
  let N := ⌊4*H*U⌋₊
  have hX0 : 0 < H*U := mul_pos hH hU
  have hN1 : 1 ≤ N := (Nat.le_floor_iff (by positivity)).mpr (by norm_num; nlinarith)
  have hNr : 0 < (N:ℝ) := by exact_mod_cast hN1
  have hN : (N:ℝ) ≤ 4*H*U := Nat.floor_le (by positivity)
  have hlogN : 0 ≤ 1+Real.log (N:ℝ) := by
    have hn : (1:ℝ) ≤ N := by exact_mod_cast hN1
    have := Real.log_nonneg hn
    linarith
  have hlog : 1+Real.log (N:ℝ) ≤ 1+Real.log (4*H*U) :=
    by linarith [Real.log_le_log hNr hN]
  have hTN : T+(N:ℝ) ≤ 4*(T+H*U) := by linarith
  unfold markedProductMeanEnvelope
  change 8*Real.exp 1*(T+(N:ℝ))*(((A/H)*(B/U))^2*(N:ℝ)*(1+Real.log (N:ℝ))^3) ≤ _
  calc
    _ ≤ 8*Real.exp 1*(4*(T+H*U))*(((A/H)*(B/U))^2*(4*H*U)*(1+Real.log (4*H*U))^3) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hTN (by positivity)
      · exact mul_le_mul (mul_le_mul_of_nonneg_left hN (sq_nonneg _))
          (pow_le_pow_left₀ hlogN hlog 3) (pow_nonneg hlogN 3) (by positivity)
      · positivity
      · positivity
    _ = _ := by field_simp; ring

 theorem marked_product_mean_envelope_uniform (σ b D : ℝ)
    (hσ : 0 ≤ σ) (hb : 0 ≤ b) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ L : ℝ in atTop, ∀ H U T : ℝ,
      0 < H → 0 < U → 1 ≤ H*U → 0 ≤ T → H*U ≤ Real.exp (σ*L) →
      T/(H*U) ≤ L^b →
      markedProductMeanEnvelope H U T
        (1+(markedSieveEulerProduct (Real.exp (L^(6/25:ℝ))))⁻¹) (L^D) ≤
          C*L^(b+2*D+5) := by
  let E := Real.exp (Real.eulerMascheroniConstant+1)
  let J := 1+Real.log 4+σ
  have hE : 0 < E := Real.exp_pos _
  have hJ : 0 < J := by dsimp [J]; have := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4); linarith
  refine ⟨256*Real.exp 1*(1+E)^2*J^3,by positivity,?_⟩
  filter_upwards [marked_rough_density_inverse_cutoff (6/25) (by norm_num),
    eventually_ge_atTop (1:ℝ)] with L hV hL
  have hLp : 0 < L := zero_lt_one.trans_le hL
  intro H U T hH hU hX hT hupper hratio
  have hV0 := markedSieveEulerProduct_pos (Real.exp (L^(6/25:ℝ)))
  have hA : 1+(markedSieveEulerProduct (Real.exp (L^(6/25:ℝ))))⁻¹ ≤ (1+E)*L := by
    have hp : L^(6/25:ℝ) ≤ L := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hL (by norm_num : (6/25:ℝ) ≤ 1)
    have hh := mul_le_mul_of_nonneg_left hp hE.le
    change (markedSieveEulerProduct (Real.exp (L^(6/25:ℝ))))⁻¹ ≤ E*L^(6/25:ℝ) at hV
    nlinarith
  have hr : 1+T/(H*U) ≤ 2*L^b := by linarith [Real.one_le_rpow hL hb]
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
    _ ≤ 128*Real.exp 1*(2*L^b)*((1+E)*L)^2*(L^D)^2*(J*L)^3 := by
      gcongr
    _ = (256*Real.exp 1*(1+E)^2*J^3)*L^(b+2*D+5) := by
      rw [show b+2*D+5=(b+2*D)+5 by ring,Real.rpow_add hLp,Real.rpow_add hLp,
        show 2*D=D*2 by ring,Real.rpow_mul hLp.le,Real.rpow_two,
        show (5:ℝ)=(5:ℕ) by norm_num,Real.rpow_natCast]
      ring

end ArtinMatthews
