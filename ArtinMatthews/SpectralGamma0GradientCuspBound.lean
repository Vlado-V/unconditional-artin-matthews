module

public import ArtinMatthews.SpectralGamma0CuspMassPositiveHeight


set_option backward.privateInPublic true
@[expose] public section

/-! The actual Dirichlet seminorm controls cusp Dirichlet energy. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups
namespace ArtinMatthews

theorem gamma0Seed_chart_gradient_le (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (δ : SL(2, ℤ)) :
    (∫ z in ModularGroup.fd, h2SectionEnergy (gamma0PoincareSeed N ψ.val) (δ⁻¹ • z)) ≤
      ‖gamma0SeedGradient N ψ‖^2 := by
  rw [gamma0SeedGradient_norm_sq]
  have he : (fun z : UpperHalfPlane => h2SectionEnergy (gamma0PoincareSeed N ψ.val) (δ⁻¹ • z)) =
      fun z => h2SectionEnergy (gamma0PoincareSeed N ψ.val)
        ((QuotientGroup.mk δ : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N).out⁻¹ • z) := by
    funext z
    exact gamma0_inverse_chart_energy_representative N ψ δ z
  rw [he]
  apply Finset.single_le_sum (s := Finset.univ)
    (a := (QuotientGroup.mk δ : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N))
    (f := fun q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N =>
      ∫ z in ModularGroup.fd, h2SectionEnergy (gamma0PoincareSeed N ψ.val) (q.out⁻¹ • z))
  · exact fun _ _ => integral_nonneg (fun _ => h2SectionEnergy_nonneg _ _)
  · exact Finset.mem_univ _

private theorem gradient_modular_embedding (δ : SL(2, ℤ)) :
    MeasurableEmbedding (fun z : UpperHalfPlane => δ • z) := by
  change MeasurableEmbedding (fun z : UpperHalfPlane => Matrix.SpecialLinearGroup.mapGL ℝ δ • z)
  exact measurableEmbedding_const_smul _

theorem gamma0_finite_cover_gradient_bound (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (r : SL(2, ℤ)) (K : Set UpperHalfPlane)
    (hK : MeasurableSet K) (s : Finset SL(2, ℤ))
    (hs : K ⊆ ⋃ δ ∈ s, (fun z : UpperHalfPlane => δ • z) ⁻¹' ModularGroup.fd) :
    IntegrableOn (fun z => h2SectionEnergy (gamma0PoincareSeed N ψ.val) (r⁻¹ • z)) K ∧
      (∫ z in K, h2SectionEnergy (gamma0PoincareSeed N ψ.val) (r⁻¹ • z)) ≤
        (s.card : ℝ)*‖gamma0SeedGradient N ψ‖^2 := by
  let f : UpperHalfPlane → ℝ := fun z => h2SectionEnergy (gamma0PoincareSeed N ψ.val) (r⁻¹ • z)
  have hc : Continuous f := (h2SectionEnergy_continuous _
    (gamma0SmoothSeed_representative_smooth N ψ)).comp
      (continuous_const_smul (Matrix.SpecialLinearGroup.mapGL ℝ r⁻¹))
  have hfd (δ : SL(2, ℤ)) : IntegrableOn (fun z => f (δ⁻¹ • z)) ModularGroup.fd := by
    have h : IntegrableOn (fun z =>
        h2SectionEnergy (gamma0PoincareSeed N ψ.val) ((δ*r)⁻¹ • z)) ModularGroup.fd :=
      arithmeticPoincareSeed_energy_integrable
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ψ
        (Matrix.SpecialLinearGroup.mapGL ℝ (δ*r)⁻¹)
    simpa only [f,mul_inv_rev,mul_smul] using h
  have hi (δ : SL(2, ℤ)) : IntegrableOn f
      ((fun z : UpperHalfPlane => δ • z) ⁻¹' ModularGroup.fd) := by
    have he := ((h2_integer_measurePreserving δ).restrict_preimage_emb
      (gradient_modular_embedding δ) ModularGroup.fd).integrable_comp_emb
        (gradient_modular_embedding δ) (g := fun z => f (δ⁻¹ • z))
    simpa only [Function.comp_def,IntegrableOn,inv_smul_smul] using he.mpr (hfd δ)
  have hb (δ : SL(2, ℤ)) :
      (∫ z in (fun z : UpperHalfPlane => δ • z) ⁻¹' ModularGroup.fd, f z) ≤
        ‖gamma0SeedGradient N ψ‖^2 := by
    have he := (h2_integer_measurePreserving δ).setIntegral_preimage_emb
      (gradient_modular_embedding δ) (fun z => f (δ⁻¹ • z)) ModularGroup.fd
    simp only [inv_smul_smul] at he
    rw [he]
    simpa only [f,mul_inv_rev,mul_smul] using gamma0Seed_chart_gradient_le N ψ (δ*r)
  have hcov := finite_cover_integrable_integral_le_sum volume s
    (fun δ : SL(2, ℤ) => (fun z : UpperHalfPlane => δ • z) ⁻¹' ModularGroup.fd)
    hK (fun δ _ => ModularGroup.isClosed_fd.measurableSet.preimage
      (h2_integer_measurePreserving δ).measurable) hs f
      (fun _ => h2SectionEnergy_nonneg _ _) hc.aestronglyMeasurable (fun δ _ => hi δ)
  refine ⟨hcov.1,hcov.2.trans ?_⟩
  calc
    _ ≤ ∑ _δ ∈ s, ‖gamma0SeedGradient N ψ‖^2 := Finset.sum_le_sum (fun δ _ => hb δ)
    _ = _ := by rw [Finset.sum_const,nsmul_eq_mul]

theorem gamma0_cusp_positive_height_gradient_bound (N : ℕ) [NeZero N]
    (Y : ℝ) (hY : 0 < Y) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ψ : h2SmoothCompactSeeds) (r : SL(2, ℤ)),
      IntegrableOn (h2SectionEnergy (gamma0CuspSection N ψ r)) (hyperbolicCuspStrip (N:ℝ) Y) ∧
      (∫ z in hyperbolicCuspStrip (N:ℝ) Y, h2SectionEnergy (gamma0CuspSection N ψ r) z) ≤
        C*‖gamma0SeedGradient N ψ‖^2 := by
  classical
  let K : Set UpperHalfPlane := {z | (z.re,z.im) ∈ spectralPlaneRectangle (N:ℝ) Y 1}
  have hK : IsCompact K := spectralCoreChart_compact (N:ℝ) Y 1 hY
  obtain ⟨sK,hsK⟩ := compact_modular_region_cover hK
  let sT : Finset SL(2, ℤ) := (Finset.Icc (0:ℤ) (N:ℤ)).image (fun k => ModularGroup.T^(-k))
  let s := sK ∪ sT
  have hcov : hyperbolicCuspStrip (N:ℝ) Y ⊆
      ⋃ δ ∈ s, (fun z : UpperHalfPlane => δ • z) ⁻¹' ModularGroup.fd := by
    intro z hz
    by_cases ht : 1 < z.im
    · obtain ⟨k,hk,hzδ⟩ := cusp_strip_modular_translation N ⟨hz.1,ht⟩
      exact mem_iUnion₂.mpr ⟨ModularGroup.T^(-k),Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨k,hk,rfl⟩),hzδ⟩
    · have hzK : z ∈ K := by
        exact ⟨⟨by have := Nat.cast_nonneg (α := ℝ) N; linarith [hz.1.1],hz.1.2⟩,
          hz.2.le,le_of_not_gt ht⟩
      obtain ⟨δ,hδ,hzδ⟩ := mem_iUnion₂.mp (hsK hzK)
      exact mem_iUnion₂.mpr ⟨δ,Finset.mem_union_left _ hδ,hzδ⟩
  have hS : MeasurableSet (hyperbolicCuspStrip (N:ℝ) Y) :=
    (measurableSet_Ioc.preimage UpperHalfPlane.continuous_re.measurable).inter
      (measurableSet_Ioi.preimage UpperHalfPlane.continuous_im.measurable)
  refine ⟨(s.card:ℝ)+1,by positivity,?_⟩
  intro ψ r
  have hb := gamma0_finite_cover_gradient_bound N ψ r _ hS s hcov
  have he : (fun z => h2SectionEnergy (gamma0PoincareSeed N ψ.val) (r⁻¹ • z)) =
      h2SectionEnergy (gamma0CuspSection N ψ r) := by
    funext z
    exact (gamma0CuspSection_energy N ψ r z).symm
  rw [he] at hb
  exact ⟨hb.1,hb.2.trans (by nlinarith [sq_nonneg ‖gamma0SeedGradient N ψ‖])⟩

end ArtinMatthews
