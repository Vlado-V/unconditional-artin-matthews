module

public import ArtinMatthews.CubicThetaUnweightedGenerators


set_option backward.privateInPublic true
@[expose] public section

/-! A concrete nonzero value of the unweighted theta fixes its finite
operator scalar when comparing transformation laws. -/
noncomputable section
namespace ArtinMatthews

open Complex UpperHalfPlane

/-- At `i`, every lattice summand is positive real and the origin contributes
one. This proves a nonzero comparison value without an automorphy assumption. -/
theorem eisensteinHolomorphicTheta_I_ne_zero :
    eisensteinHolomorphicTheta UpperHalfPlane.I ≠ 0 := by
  let g : ℤ × ℤ → ℝ := fun z => Real.exp (-2 * Real.pi *
    ((z.1 : ℝ) ^ 2 - (z.1 : ℝ) * (z.2 : ℝ) + (z.2 : ℝ) ^ 2))
  have ht (z : ℤ × ℤ) : eisensteinComplexGaussian 2 z = (g z : ℂ) := by
    rw [eisensteinComplexGaussian]
    dsimp only [g]
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  have hs : Summable g := by
    have h := (eisensteinComplexGaussian_summable (show 0 < (2 : ℂ).re by norm_num)).norm
    apply h.congr
    intro z
    rw [ht]
    exact Complex.norm_of_nonneg (Real.exp_pos _).le
  have hsum : 1 ≤ ∑' z, g z := by
    have h := hs.le_tsum (0, 0) (fun z _ => (Real.exp_pos _).le)
    simpa [g] using h
  have he : eisensteinHolomorphicTheta UpperHalfPlane.I = ((∑' z, g z : ℝ) : ℂ) := by
    rw [eisensteinHolomorphicTheta_eq_gaussian]
    have hp : eisensteinGaussianParameter UpperHalfPlane.I = 2 := by
      norm_num [eisensteinGaussianParameter, UpperHalfPlane.I, mul_assoc]
    rw [hp, Complex.ofReal_tsum]
    exact tsum_congr ht
  rw [he]
  exact Complex.ofReal_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le zero_lt_one hsum))

end ArtinMatthews
