module

public import ArtinMatthews.SpectralCuspDoubleCosetPeriod
public import ArtinMatthews.SpectralGamma0PoincareSpectral
public import ArtinMatthews.SpectralCompactChartCover


set_option backward.privateInPublic true
@[expose] public section

/-! Actual geometric kernels for two compact smooth Poincare tests.  Proper
discontinuity supplies a single finite set of contributing matrices, so the
sum/integral interchange introduces no convergence assumption. -/

noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups InnerProductSpace Pointwise

namespace ArtinMatthews

theorem integer_compact_translates_finite {K L : Set UpperHalfPlane}
    (hK : IsCompact K) (hL : IsCompact L) :
    {M : SL(2, ℤ) | ((M • K) ∩ L).Nonempty}.Finite := by
  let ι : SL(2, ℤ) → 𝒮ℒ := fun M => ⟨Matrix.SpecialLinearGroup.mapGL ℝ M, ⟨M, rfl⟩⟩
  have hinj : Function.Injective ι := by
    intro M R h
    apply Matrix.SpecialLinearGroup.mapGL_injective (S := ℝ)
    exact congrArg Subtype.val h
  apply (Set.Finite.preimage hinj.injOn (finite_disjoint_inter_image (Γ := 𝒮ℒ) hK hL)).subset
  intro M hM
  exact hM

def compactPoincareGeometricKernel (ψ φ : h2SmoothCompactSeeds) (M : SL(2, ℤ)) : ℂ :=
  ∫ z : UpperHalfPlane, inner ℂ (ψ.val z) (φ.val (M • z))

theorem compactPoincareGeometricKernel_integrable (ψ φ : h2SmoothCompactSeeds)
    (M : SL(2, ℤ)) :
    Integrable (fun z : UpperHalfPlane => inner ℂ (ψ.val z) (φ.val (M • z))) :=
  h2_compactSeed_inner_integrable ψ _
    (φ.val.continuous.comp (continuous_const_smul (Matrix.SpecialLinearGroup.mapGL ℝ M)))

theorem compactPoincare_contributing_matrices_finite (N : ℕ)
    (r s : SL(2, ℤ)) (ψ φ : h2SmoothCompactSeeds) :
    {γ : CongruenceSubgroup.Gamma0 N | ∃ z ∈ tsupport ψ.val,
      (s * (γ : SL(2, ℤ)) * r⁻¹) • z ∈ tsupport φ.val}.Finite := by
  have hinj : Function.Injective (fun γ : CongruenceSubgroup.Gamma0 N =>
      s * (γ : SL(2, ℤ)) * r⁻¹) := by
    intro γ δ h
    apply Subtype.ext
    exact mul_left_cancel (mul_right_cancel h)
  apply ((integer_compact_translates_finite ψ.val.hasCompactSupport φ.val.hasCompactSupport).preimage
    hinj.injOn).subset
  rintro γ ⟨z,hz,hφ⟩
  exact ⟨(s * (γ : SL(2, ℤ)) * r⁻¹) • z, ⟨⟨z,hz,rfl⟩,hφ⟩⟩

theorem gamma0CuspSection_translated_finsum (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (φ : h2SmoothCompactSeeds) (z : UpperHalfPlane) :
    gamma0CuspSection N (modularTranslateSmoothSeed s φ) r z =
      ∑ᶠ γ : CongruenceSubgroup.Gamma0 N, φ.val ((s * (γ : SL(2, ℤ)) * r⁻¹) • z) := by
  rw [gamma0CuspSection, gamma0PoincareSeed_eq_finsum]
  simp only [modularTranslateSmoothSeed_apply, mul_smul]

theorem compactPoincareGeometricKernel_hasFiniteSupport (N : ℕ)
    (r s : SL(2, ℤ)) (ψ φ : h2SmoothCompactSeeds) :
    Function.HasFiniteSupport (fun γ : CongruenceSubgroup.Gamma0 N =>
      compactPoincareGeometricKernel ψ φ (s * (γ : SL(2, ℤ)) * r⁻¹)) := by
  apply (compactPoincare_contributing_matrices_finite N r s ψ φ).subset
  intro γ hγ
  by_contra hnot
  apply hγ
  apply integral_eq_zero_of_ae
  filter_upwards [] with z
  simp only [Pi.zero_apply]
  by_cases hψ : ψ.val z = 0
  · rw [hψ, inner_zero_left]
  by_cases hφ : φ.val ((s * (γ : SL(2, ℤ)) * r⁻¹) • z) = 0
  · rw [hφ, inner_zero_right]
  exact False.elim (hnot ⟨z,subset_tsupport _ hψ,subset_tsupport _ hφ⟩)

theorem gamma0_compact_pairing_integral_finsum (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (ψ φ : h2SmoothCompactSeeds) :
    (∫ z : UpperHalfPlane, inner ℂ (ψ.val z)
      (gamma0CuspSection N (modularTranslateSmoothSeed s φ) r z)) =
      ∑ᶠ γ : CongruenceSubgroup.Gamma0 N,
        compactPoincareGeometricKernel ψ φ (s * (γ : SL(2, ℤ)) * r⁻¹) := by
  classical
  let hf := compactPoincare_contributing_matrices_finite N r s ψ φ
  let t := hf.toFinset
  have hpoint (z : UpperHalfPlane) :
      inner ℂ (ψ.val z) (gamma0CuspSection N (modularTranslateSmoothSeed s φ) r z) =
      ∑ γ ∈ t, inner ℂ (ψ.val z) (φ.val ((s * (γ : SL(2, ℤ)) * r⁻¹) • z)) := by
    rw [gamma0CuspSection_translated_finsum]
    simp only [RCLike.inner_apply]
    rw [finsum_mul]
    apply finsum_eq_sum_of_support_subset
    intro γ hγ
    apply hf.mem_toFinset.mpr
    have hn := mul_ne_zero_iff.mp hγ
    have hψ : ψ.val z ≠ 0 := by
      intro hz
      exact hn.2 (by rw [hz]; simp)
    exact ⟨z,subset_tsupport _ hψ,subset_tsupport _ hn.1⟩
  have hsupp : Function.support (fun γ : CongruenceSubgroup.Gamma0 N =>
      compactPoincareGeometricKernel ψ φ (s * (γ : SL(2, ℤ)) * r⁻¹)) ⊆ t := by
    intro γ hγ
    by_contra hnot
    apply hγ
    apply integral_eq_zero_of_ae
    filter_upwards [] with z
    simp only [Pi.zero_apply]
    by_cases hz : ψ.val z = 0
    · rw [hz,inner_zero_left]
    have hφ : φ.val ((s * (γ : SL(2, ℤ)) * r⁻¹) • z) = 0 := by
      by_contra hφ
      exact hnot (hf.mem_toFinset.mpr ⟨z,subset_tsupport _ hz,subset_tsupport _ hφ⟩)
    rw [hφ,inner_zero_right]
  calc
    _ = ∫ z : UpperHalfPlane, ∑ γ ∈ t,
        inner ℂ (ψ.val z) (φ.val ((s * (γ : SL(2, ℤ)) * r⁻¹) • z)) := by
      apply integral_congr_ae
      exact Eventually.of_forall hpoint
    _ = ∑ γ ∈ t, compactPoincareGeometricKernel ψ φ (s * (γ : SL(2, ℤ)) * r⁻¹) :=
      integral_finsetSum t (fun γ _ => compactPoincareGeometricKernel_integrable ψ φ _)
    _ = _ := (finsum_eq_sum_of_support_subset _ hsupp).symm

theorem gamma0SmoothSeedMass_pairing_geometric (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (ψ φ : h2SmoothCompactSeeds) :
    inner ℂ (gamma0SmoothSeedMass N (modularTranslateSmoothSeed r ψ))
      (gamma0SmoothSeedMass N (modularTranslateSmoothSeed s φ)) =
      2 * ∑ᶠ M : gamma0CuspCorrespondence N r s, compactPoincareGeometricKernel ψ φ M.val := by
  rw [gamma0SmoothSeedMass_inner_unfold_translated, gamma0_compact_pairing_integral_finsum]
  congr 1
  exact finsum_comp_equiv (f := fun M : gamma0CuspCorrespondence N r s =>
    compactPoincareGeometricKernel ψ φ M.val) (gamma0CuspMatrixEquiv N r s)

theorem compactPoincareGeometricKernel_neg (ψ φ : h2SmoothCompactSeeds) (M : SL(2, ℤ)) :
    compactPoincareGeometricKernel ψ φ (-M) = compactPoincareGeometricKernel ψ φ M := by
  unfold compactPoincareGeometricKernel
  simp only [ModularGroup.SL_neg_smul]

end ArtinMatthews
