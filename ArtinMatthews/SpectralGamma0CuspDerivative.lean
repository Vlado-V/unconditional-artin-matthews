module

public import ArtinMatthews.SpectralGamma0CuspRestriction


set_option backward.privateInPublic true
@[expose] public section

/-! The actual horizontal derivative map, bounded by the genuine global energy. -/

noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups ContDiff

namespace ArtinMatthews

theorem gamma0CuspSmoothCore_add (N : ℕ) [NeZero N] (ψ ξ : h2SmoothCompactSeeds)
    (r : SL(2, ℤ)) :
    (gamma0CuspSmoothCore N (ψ+ξ) r).toFun =
      (gamma0CuspSmoothCore N ψ r).toFun+(gamma0CuspSmoothCore N ξ r).toFun := by
  funext p
  change (spectralHeightTransition 1 p.2 : ℂ)*
    arithmeticPoincareSeed _ (ψ.val+ξ.val) _ =
      (spectralHeightTransition 1 p.2 : ℂ)*arithmeticPoincareSeed _ ψ.val _+
      (spectralHeightTransition 1 p.2 : ℂ)*arithmeticPoincareSeed _ ξ.val _
  rw [arithmeticPoincareSeed_add]
  exact mul_add _ _ _

theorem gamma0CuspSmoothCore_smul (N : ℕ) [NeZero N] (c : ℂ) (ψ : h2SmoothCompactSeeds)
    (r : SL(2, ℤ)) :
    (gamma0CuspSmoothCore N (c • ψ) r).toFun = c • (gamma0CuspSmoothCore N ψ r).toFun := by
  funext p
  change (spectralHeightTransition 1 p.2 : ℂ)*arithmeticPoincareSeed _ (c • ψ.val) _ =
    c*((spectralHeightTransition 1 p.2 : ℂ)*arithmeticPoincareSeed _ ψ.val _)
  rw [arithmeticPoincareSeed_smul]
  change _ * (c * _) = c * (_ * _)
  ring

private theorem partialX_add {F G : ℝ × ℝ → ℂ}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (p : ℝ × ℝ) :
    spectralPlanePartialX (F+G) p = spectralPlanePartialX F p+spectralPlanePartialX G p := by
  have hx : ContDiff ℝ ∞ (fun x : ℝ => (x,p.2)) := contDiff_id.prodMk contDiff_const
  exact deriv_add ((hF.comp hx).differentiable (by simp) p.1)
    ((hG.comp hx).differentiable (by simp) p.1)

private theorem partialX_smul {F : ℝ × ℝ → ℂ}
    (hF : ContDiff ℝ ∞ F) (c : ℂ) (p : ℝ × ℝ) :
    spectralPlanePartialX (c • F) p = c • spectralPlanePartialX F p := by
  have hx : ContDiff ℝ ∞ (fun x : ℝ => (x,p.2)) := contDiff_id.prodMk contDiff_const
  exact deriv_const_smul c ((hF.comp hx).differentiable (by simp) p.1)

def gamma0CuspSeedDerivative (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds) (r : SL(2, ℤ)) :
    Lp ℂ 2 (spectralCuspEuclideanMeasure (N : ℝ) 1) :=
  spectralCuspDerivativeLp (gamma0CuspSmoothCore N ψ r).smooth
    (Nat.cast_pos.mpr (NeZero.pos N)) (gamma0CuspSmoothCore N ψ r).energy_integrable

theorem gamma0CuspSeedDerivative_ae (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds) (r : SL(2, ℤ)) :
    gamma0CuspSeedDerivative N ψ r =ᵐ[spectralCuspEuclideanMeasure (N : ℝ) 1]
      spectralPlanePartialX (gamma0CuspSmoothCore N ψ r).toFun :=
  MemLp.coeFn_toLp (spectral_cusp_derivative_memLp (gamma0CuspSmoothCore N ψ r).smooth
    (Nat.cast_pos.mpr (NeZero.pos N)) (gamma0CuspSmoothCore N ψ r).energy_integrable)

theorem gamma0CuspSeedDerivative_norm_sq_bound (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (r : SL(2, ℤ)) :
    ‖gamma0CuspSeedDerivative N ψ r‖^2 ≤ ((N : ℝ)+1)*‖gamma0EnergyTest N ψ‖^2 := by
  rw [gamma0CuspSeedDerivative,spectralCuspDerivativeLp_norm_square]
  exact gamma0CuspSmoothCore_energy_bound N ψ r

theorem gamma0CuspSeedDerivative_norm_bound (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (r : SL(2, ℤ)) :
    ‖gamma0CuspSeedDerivative N ψ r‖ ≤ Real.sqrt ((N : ℝ)+1)*‖gamma0EnergyTest N ψ‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow,Real.sq_sqrt (by positivity : 0 ≤ (N : ℝ)+1)]
  exact gamma0CuspSeedDerivative_norm_sq_bound N ψ r

def gamma0CuspDerivativeLinear (N : ℕ) [NeZero N] (r : SL(2, ℤ)) :
    h2SmoothCompactSeeds →ₗ[ℂ] Lp ℂ 2 (spectralCuspEuclideanMeasure (N : ℝ) 1) where
  toFun ψ := gamma0CuspSeedDerivative N ψ r
  map_add' ψ ξ := by
    apply Lp.ext
    filter_upwards [gamma0CuspSeedDerivative_ae N (ψ+ξ) r,gamma0CuspSeedDerivative_ae N ψ r,
      gamma0CuspSeedDerivative_ae N ξ r,
      Lp.coeFn_add (gamma0CuspSeedDerivative N ψ r) (gamma0CuspSeedDerivative N ξ r)]
      with z hs hψ hξ hadd
    rw [hadd,hs]
    change _ = (gamma0CuspSeedDerivative N ψ r) z+(gamma0CuspSeedDerivative N ξ r) z
    rw [hψ,hξ,gamma0CuspSmoothCore_add]
    exact partialX_add (gamma0CuspSmoothCore N ψ r).smooth (gamma0CuspSmoothCore N ξ r).smooth z
  map_smul' c ψ := by
    apply Lp.ext
    filter_upwards [gamma0CuspSeedDerivative_ae N (c • ψ) r,gamma0CuspSeedDerivative_ae N ψ r,
      Lp.coeFn_smul c (gamma0CuspSeedDerivative N ψ r)] with z hs hψ hsmul
    simp only [RingHom.id_apply]
    rw [hsmul,hs]
    change _ = c • (gamma0CuspSeedDerivative N ψ r) z
    rw [hψ,gamma0CuspSmoothCore_smul]
    exact partialX_smul (gamma0CuspSmoothCore N ψ r).smooth c z

private theorem derivative_seed_bound (N : ℕ) [NeZero N] (r : SL(2, ℤ)) :
    ∃ C : ℝ, ∀ ψ : h2SmoothCompactSeeds,
      ‖gamma0CuspDerivativeLinear N r ψ‖ ≤ C * ‖gamma0EnergyTestLinear N ψ‖ :=
  ⟨Real.sqrt ((N : ℝ)+1),fun ψ => gamma0CuspSeedDerivative_norm_bound N ψ r⟩

private theorem derivative_extension_exists (N : ℕ) [NeZero N] (r : SL(2, ℤ)) :
    ∃ A : gamma0EnergySpace N →L[ℂ] Lp ℂ 2 (spectralCuspEuclideanMeasure (N : ℝ) 1),
      ∀ ψ, A (gamma0EnergyTestLinear N ψ) = gamma0CuspDerivativeLinear N r ψ :=
  exists_bounded_extension_of_dense_functions (D := h2SmoothCompactSeeds)
    (gamma0CuspDerivativeLinear N r) (gamma0EnergyTestLinear N) (gamma0EnergyTest_dense N)
    (gamma0CuspDerivativeLinear N r).map_add (gamma0CuspDerivativeLinear N r).map_smul
    (gamma0EnergyTestLinear N).map_add (gamma0EnergyTestLinear N).map_smul
    (derivative_seed_bound N r)

def gamma0CuspEnergyDerivative (N : ℕ) [NeZero N] (r : SL(2, ℤ)) :
    gamma0EnergySpace N →L[ℂ] Lp ℂ 2 (spectralCuspEuclideanMeasure (N : ℝ) 1) :=
  (derivative_extension_exists N r).choose

theorem gamma0CuspEnergyDerivative_apply (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (ψ : h2SmoothCompactSeeds) :
    gamma0CuspEnergyDerivative N r (gamma0EnergyTest N ψ) = gamma0CuspSeedDerivative N ψ r :=
  (derivative_extension_exists N r).choose_spec ψ

theorem gamma0CuspEnergyDerivative_norm_bound (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (u : gamma0EnergySpace N) :
    ‖gamma0CuspEnergyDerivative N r u‖ ≤ Real.sqrt ((N : ℝ)+1)*‖u‖ := by
  apply isClosed_property (gamma0EnergyTest_dense N)
    (isClosed_le (gamma0CuspEnergyDerivative N r).continuous.norm
      (continuous_const.mul continuous_norm))
  intro ψ
  change ‖gamma0CuspEnergyDerivative N r (gamma0EnergyTest N ψ)‖ ≤ _
  rw [gamma0CuspEnergyDerivative_apply]
  exact gamma0CuspSeedDerivative_norm_bound N ψ r

end ArtinMatthews
