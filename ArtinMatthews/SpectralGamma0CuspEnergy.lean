module

public import ArtinMatthews.SpectralCuspModularCover
public import ArtinMatthews.SpectralGamma0CosetCharts
public import ArtinMatthews.SpectralFiniteCoverIntegral
public import Mathlib.MeasureTheory.Group.Integral


set_option backward.privateInPublic true
@[expose] public section

/-! Actual global control of the unbounded cusp period strips. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups

namespace ArtinMatthews

/-- Every integral cusp's complete period strip has integrable actual mass
and energy, bounded by N+1 times the genuine global core energy. -/
theorem gamma0_cusp_strip_energy_bound (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (r : SL(2, ℤ)) :
    IntegrableOn (fun z : UpperHalfPlane =>
      ‖gamma0PoincareSeed N ψ.val (r⁻¹ • z)‖ ^ 2 +
      h2SectionEnergy (gamma0PoincareSeed N ψ.val) (r⁻¹ • z))
      (hyperbolicCuspStrip (N : ℝ) 1) ∧
    (∫ z in hyperbolicCuspStrip (N : ℝ) 1,
      ‖gamma0PoincareSeed N ψ.val (r⁻¹ • z)‖ ^ 2 +
      h2SectionEnergy (gamma0PoincareSeed N ψ.val) (r⁻¹ • z)) ≤
      ((N : ℝ) + 1) * ‖gamma0EnergyTest N ψ‖ ^ 2 := by
  classical
  let f : UpperHalfPlane → ℝ := fun z =>
    ‖gamma0PoincareSeed N ψ.val (r⁻¹ • z)‖ ^ 2 +
      h2SectionEnergy (gamma0PoincareSeed N ψ.val) (r⁻¹ • z)
  have hc : Continuous f := by
    have h := ((gamma0PoincareSeed N ψ.val).continuous.norm.pow 2).add
      (h2SectionEnergy_continuous _ (gamma0SmoothSeed_representative_smooth N ψ))
    change Continuous ((fun z : UpperHalfPlane =>
      ‖gamma0PoincareSeed N ψ.val z‖ ^ 2 + h2SectionEnergy (gamma0PoincareSeed N ψ.val) z) ∘
      fun z => Matrix.SpecialLinearGroup.mapGL ℝ r⁻¹ • z)
    exact h.comp (continuous_const_smul _)
  have hmp (δ : SL(2, ℤ)) : MeasurePreserving (fun z : UpperHalfPlane => δ • z) volume volume := by
    change MeasurePreserving (fun z : UpperHalfPlane => Matrix.SpecialLinearGroup.mapGL ℝ δ • z) _ _
    exact measurePreserving_smul _ _
  have hme (δ : SL(2, ℤ)) : MeasurableEmbedding (fun z : UpperHalfPlane => δ • z) := by
    change MeasurableEmbedding (fun z : UpperHalfPlane => Matrix.SpecialLinearGroup.mapGL ℝ δ • z)
    exact measurableEmbedding_const_smul _
  have hfd (δ : SL(2, ℤ)) : IntegrableOn (fun z : UpperHalfPlane => f (δ⁻¹ • z)) ModularGroup.fd := by
    have h : IntegrableOn (fun z : UpperHalfPlane =>
        ‖gamma0PoincareSeed N ψ.val ((δ * r)⁻¹ • z)‖ ^ 2 +
        h2SectionEnergy (gamma0PoincareSeed N ψ.val) ((δ * r)⁻¹ • z)) ModularGroup.fd :=
      ((gamma0PoincareSeed_memLp_modularRegion N ψ.val (δ * r)⁻¹).integrable_norm_pow
      (by norm_num)).add (arithmeticPoincareSeed_energy_integrable
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ψ
        (Matrix.SpecialLinearGroup.mapGL ℝ (δ * r)⁻¹))
    simpa only [f, mul_inv_rev, mul_smul] using h
  have hi (δ : SL(2, ℤ)) : IntegrableOn f
      ((fun z : UpperHalfPlane => δ • z) ⁻¹' ModularGroup.fd) := by
    have he := ((hmp δ).restrict_preimage_emb (hme δ) ModularGroup.fd).integrable_comp_emb
      (hme δ) (g := fun z => f (δ⁻¹ • z))
    simpa only [Function.comp_def, IntegrableOn, inv_smul_smul] using he.mpr (hfd δ)
  have hbound (δ : SL(2, ℤ)) :
      (∫ z in (fun z : UpperHalfPlane => δ • z) ⁻¹' ModularGroup.fd, f z) ≤
        ‖gamma0EnergyTest N ψ‖ ^ 2 := by
    have he := (hmp δ).setIntegral_preimage_emb (hme δ) (fun z => f (δ⁻¹ • z)) ModularGroup.fd
    simp only [inv_smul_smul] at he
    rw [he]
    simpa only [f, mul_inv_rev, mul_smul] using gamma0Seed_chart_energy_le N ψ (δ * r)
  have hK : MeasurableSet (hyperbolicCuspStrip (N : ℝ) 1) :=
    (measurableSet_Ioc.preimage UpperHalfPlane.continuous_re.measurable).inter
      (measurableSet_Ioi.preimage UpperHalfPlane.continuous_im.measurable)
  have hcov := finite_cover_integrable_integral_le_sum volume
    (Finset.Icc (0 : ℤ) (N : ℤ))
    (fun k : ℤ => (fun z : UpperHalfPlane => ModularGroup.T ^ (-k) • z) ⁻¹' ModularGroup.fd)
    hK (fun k _ => ModularGroup.isClosed_fd.measurableSet.preimage (hmp _).measurable)
    (cusp_strip_modular_cover N) f
    (fun z => add_nonneg (sq_nonneg _) (h2SectionEnergy_nonneg _ _))
    hc.aestronglyMeasurable (fun k _ => hi _)
  refine ⟨hcov.1, hcov.2.trans ?_⟩
  calc
    _ ≤ ∑ _k ∈ Finset.Icc (0 : ℤ) (N : ℤ), ‖gamma0EnergyTest N ψ‖ ^ 2 :=
      Finset.sum_le_sum (fun k _ => hbound _)
    _ = ((N : ℝ) + 1) * ‖gamma0EnergyTest N ψ‖ ^ 2 := by
      have hcard : (Finset.Icc (0 : ℤ) (N : ℤ)).card = N + 1 := by
        rw [Int.card_Icc]
        omega
      rw [Finset.sum_const, hcard, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]

end ArtinMatthews
