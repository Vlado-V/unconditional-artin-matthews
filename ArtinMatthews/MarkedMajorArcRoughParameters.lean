module

public import ArtinMatthews.MarkedMajorArcRoughMertens
public import ArtinMatthews.MarkedRoughCharacterRange


set_option backward.privateInPublic true
@[expose] public section

/-! The actual Mertens density supplies the polynomial hypothesis in the
rough-character envelope, uniformly over the modulus. -/
namespace ArtinMatthews
open Filter
open scoped Topology

 theorem marked_rough_modulus_density_budget (a κ : ℝ) (hκ : 0 < κ) :
    ∀ᶠ L : ℝ in atTop, ∀ q : ℝ, 0 ≤ q → q ≤ L^a →
      q*(markedSieveEulerProduct (Real.exp (L^κ)))⁻¹ /
        markedSieveEulerProduct (Real.exp (L^κ)) ≤
      (Real.exp (Real.eulerMascheroniConstant+1))^2 * L^(a+2*κ) := by
  filter_upwards [marked_rough_density_inverse_cutoff κ hκ,
    eventually_gt_atTop (0:ℝ)] with L hV Lpos
  intro q hq hqhi
  let V := markedSieveEulerProduct (Real.exp (L^κ))
  let E := Real.exp (Real.eulerMascheroniConstant+1)
  have hVp : 0 < V := markedSieveEulerProduct_pos _
  have hVi : 0 ≤ V⁻¹ := inv_nonneg.mpr hVp.le
  have he : 0 ≤ E*L^κ := by dsimp [E]; positivity
  have hsq : (V⁻¹)^2 ≤ (E*L^κ)^2 := by
    exact pow_le_pow_left₀ hVi hV 2
  have hpow : L^(a+2*κ)=L^a*(L^κ)^2 := by
    rw [Real.rpow_add Lpos,show 2*κ=κ*2 by ring,Real.rpow_mul Lpos.le,Real.rpow_two]
  calc
    _ = q*(V⁻¹)^2 := by dsimp [V]; ring
    _ ≤ L^a*(E*L^κ)^2 := mul_le_mul hqhi hsq (sq_nonneg _) (Real.rpow_nonneg Lpos.le _)
    _ = _ := by rw [hpow]; dsimp [E]; ring

end ArtinMatthews
