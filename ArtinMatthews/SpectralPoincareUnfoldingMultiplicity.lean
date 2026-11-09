module

public import ArtinMatthews.SpectralModularPartition


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine modular interior cover has multiplicity exactly two under
`SL(2, ℤ)`, from its two central signs.  This is an almost-everywhere pointwise
identity, proved without asserting that the action is free. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups

namespace ArtinMatthews

theorem modular_fdo_indicator_finsum (F : UpperHalfPlane → ℂ)
    {z : UpperHalfPlane} (hz : ∃ g : SL(2, ℤ), g • z ∈ ModularGroup.fdo) :
    (∑ᶠ g : SL(2, ℤ), ((fun w : UpperHalfPlane => g • w) ⁻¹' ModularGroup.fdo).indicator F z) =
      2 * F z := by
  classical
  obtain ⟨g, hg⟩ := hz
  have hne : g ≠ -g := by
    intro h
    have he := congrArg (fun a : SL(2, ℤ) => a * g⁻¹) h
    have hsign : (1 : SL(2, ℤ)) = -1 := by simpa only [neg_mul, mul_inv_cancel] using he
    have he' := congrArg (fun a : SL(2, ℤ) => a 0 0) hsign
    norm_num at he'
  have hs : Function.support (fun δ : SL(2, ℤ) =>
      ((fun w : UpperHalfPlane => δ • w) ⁻¹' ModularGroup.fdo).indicator F z) ⊆
        ({g, -g} : Finset SL(2, ℤ)) := by
    intro δ hδ
    have hδz : δ • z ∈ ModularGroup.fdo := by
      by_contra h
      exact hδ (indicator_of_notMem
        (show z ∉ (fun w : UpperHalfPlane => δ • w) ⁻¹' ModularGroup.fdo from h) F)
    have hc := modular_interior_overlap_central hg (ModularGroup.fdo_subset_fd hδz)
    rcases hc with hc | hc
    · have he := congrArg (fun a : SL(2, ℤ) => a * g) hc
      have hd : δ = g := by simpa only [mul_assoc, inv_mul_cancel, mul_one, one_mul] using he
      exact Finset.mem_insert.mpr (Or.inl hd)
    · have he := congrArg (fun a : SL(2, ℤ) => a * g) hc
      have hd : δ = -g := by simpa only [mul_assoc, inv_mul_cancel, mul_one, neg_one_mul] using he
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr hd))
  rw [finsum_eq_sum_of_support_subset _ hs, Finset.sum_pair hne]
  have hng : (-g) • z ∈ ModularGroup.fdo := by
    rw [ModularGroup.SL_neg_smul]
    exact hg
  rw [indicator_of_mem
    (show z ∈ (fun w : UpperHalfPlane => g • w) ⁻¹' ModularGroup.fdo from hg),
    indicator_of_mem
    (show z ∈ (fun w : UpperHalfPlane => (-g) • w) ⁻¹' ModularGroup.fdo from hng), two_mul]

theorem modular_fdo_indicator_finsum_ae (F : UpperHalfPlane → ℂ) :
    ∀ᵐ z : UpperHalfPlane ∂volume,
      (∑ᶠ g : SL(2, ℤ),
        ((fun w : UpperHalfPlane => g • w) ⁻¹' ModularGroup.fdo).indicator F z) = 2 * F z := by
  filter_upwards [modular_exists_smul_mem_fdo_ae] with z hz
  exact modular_fdo_indicator_finsum F hz

end ArtinMatthews
