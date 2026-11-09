module

public import ArtinMatthews.SpectralCompactChartHeight


set_option backward.privateInPublic true
@[expose] public section

/-! A genuine finite modular-region cover of any compact H² chart. -/

noncomputable section
open Set
open scoped MatrixGroups Pointwise

namespace ArtinMatthews

/-- Compact charts meet only finitely many modular regions, including boundary
multiplicities.  This follows from actual proper discontinuity and height
control, and does not assume an almost-everywhere partition. -/
theorem compact_modular_translates_meeting_fd_finite {K : Set UpperHalfPlane}
    (hK : IsCompact K) :
    {δ : SL(2, ℤ) | ((δ • K) ∩ ModularGroup.fd).Nonempty}.Finite := by
  obtain ⟨Y, _, hY⟩ := compact_modular_images_height_bound hK
  let ι : SL(2, ℤ) → 𝒮ℒ := fun δ => ⟨Matrix.SpecialLinearGroup.mapGL ℝ δ, ⟨δ, rfl⟩⟩
  have hι : Function.Injective ι := by
    intro δ ε h
    apply Matrix.SpecialLinearGroup.mapGL_injective (S := ℝ)
    exact congrArg Subtype.val h
  have hf := finite_disjoint_inter_image (Γ := 𝒮ℒ) hK
    (ModularGroup.isCompact_truncatedFundamentalDomain Y)
  apply (Set.Finite.preimage hι.injOn hf).subset
  intro δ hδ
  obtain ⟨w, ⟨z, hz, rfl⟩, hw⟩ := hδ
  change (((ι δ) • K) ∩ ModularGroup.truncatedFundamentalDomain Y).Nonempty
  exact ⟨δ • z, ⟨⟨z, hz, rfl⟩, hw, hY δ z hz⟩⟩

/-- Explicit finite-cover form for integration and localization. -/
theorem compact_modular_region_cover {K : Set UpperHalfPlane} (hK : IsCompact K) :
    ∃ s : Finset SL(2, ℤ),
      K ⊆ ⋃ δ ∈ s, (fun z : UpperHalfPlane => δ • z) ⁻¹' ModularGroup.fd := by
  classical
  let hfinite := compact_modular_translates_meeting_fd_finite hK
  refine ⟨hfinite.toFinset, fun z hz => ?_⟩
  obtain ⟨δ, hδ⟩ := ModularGroup.exists_smul_mem_fd z
  apply mem_iUnion₂.mpr
  refine ⟨δ, hfinite.mem_toFinset.mpr ?_, hδ⟩
  exact ⟨δ • z, ⟨z, hz, rfl⟩, hδ⟩

end ArtinMatthews
