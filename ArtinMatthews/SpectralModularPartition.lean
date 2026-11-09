module

public import ArtinMatthews.SpectralModularBoundary
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.Basic.Countable.Basic


set_option backward.privateInPublic true
@[expose] public section

/-!
The standard modular interiors cover almost every point and have precisely
the central `±1` ambiguity.  In particular, inverse representatives of distinct
right `Γ₀(N)` cosets are disjoint even after applying an element of `Γ₀(N)`.
No freeness of the `SL(2, ℤ)` action is asserted.
-/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups

namespace ArtinMatthews

private theorem modular_smul_measurePreserving (g : SL(2, ℤ)) :
    MeasurePreserving (fun z : UpperHalfPlane => g • z) volume volume := by
  change MeasurePreserving
    (fun z : UpperHalfPlane => Matrix.SpecialLinearGroup.mapGL ℝ g • z) _ _
  exact measurePreserving_smul _ _

/-- Simultaneously for every modular translate, membership in the closed
region agrees with membership in its interior almost everywhere. -/
theorem modular_translates_fd_to_fdo_ae :
    ∀ᵐ z : UpperHalfPlane ∂volume, ∀ g : SL(2, ℤ),
      g • z ∈ ModularGroup.fd → g • z ∈ ModularGroup.fdo := by
  let : Countable (Matrix (Fin 2) (Fin 2) ℤ) :=
    inferInstanceAs (Countable (Fin 2 → Fin 2 → ℤ))
  let : Countable (SL(2, ℤ)) :=
    (show Function.Injective (fun g : SL(2, ℤ) => g.val) from Subtype.val_injective).countable
  rw [ae_all_iff]
  intro g
  have hnull := (modular_smul_measurePreserving g).quasiMeasurePreserving.preimage_null
    modular_fd_sdiff_fdo_volume_zero
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with z hz hfd
  by_contra hnot
  exact hz ⟨hfd, hnot⟩

/-- The interiors of actual modular translates cover almost every point. -/
theorem modular_exists_smul_mem_fdo_ae :
    ∀ᵐ z : UpperHalfPlane ∂volume, ∃ g : SL(2, ℤ), g • z ∈ ModularGroup.fdo := by
  filter_upwards [modular_translates_fd_to_fdo_ae] with z hz
  obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd z
  exact ⟨g, hz g hg⟩

/-- An overlap between a translated interior and a translated closed domain
forces the exact central ambiguity. -/
theorem modular_interior_overlap_central {g h : SL(2, ℤ)} {z : UpperHalfPlane}
    (hg : g • z ∈ ModularGroup.fdo) (hh : h • z ∈ ModularGroup.fd) :
    h * g⁻¹ = 1 ∨ h * g⁻¹ = -1 := by
  apply ModularGroup.eq_one_or_neg_one_of_mem_fdo_mem_fd hg
  simpa only [mul_smul, inv_smul_smul] using hh

/-- A subgroup containing the central `-1` identifies every overlap of two
interior charts after its own action.  This is the precise coset partition
statement required for constructing independent chart data. -/
theorem modular_interior_overlap_quotient_eq
    (H : Subgroup (SL(2, ℤ))) (hneg : (-1 : SL(2, ℤ)) ∈ H)
    {r s γ : SL(2, ℤ)} (hγ : γ ∈ H) {z : UpperHalfPlane}
    (hr : r • z ∈ ModularGroup.fdo)
    (hs : s • (γ • z) ∈ ModularGroup.fdo) :
    (r : SL(2, ℤ) ⧸ H) = s := by
  have hcentral : (s * γ) * r⁻¹ = 1 ∨ (s * γ) * r⁻¹ = -1 :=
    modular_interior_overlap_central hr
      (ModularGroup.fdo_subset_fd (by simpa only [mul_smul] using hs))
  apply QuotientGroup.eq.mpr
  rcases hcentral with h | h
  · have heq : s * γ = r := by
      have := congrArg (fun u : SL(2, ℤ) => u * r) h
      simpa only [mul_assoc, inv_mul_cancel, mul_one, one_mul] using this
    have hmem : s⁻¹ * r ∈ H := by simpa only [← heq, inv_mul_cancel_left] using hγ
    simpa only [mul_inv_rev, inv_inv] using H.inv_mem hmem
  · have heq : s * γ = -r := by
      have := congrArg (fun u : SL(2, ℤ) => u * r) h
      simpa only [mul_assoc, inv_mul_cancel, mul_one, neg_one_mul] using this
    have hmem : s⁻¹ * r ∈ H := by
      have hmul := H.mul_mem hneg hγ
      convert hmul using 1
      rw [neg_one_mul]
      apply (mul_left_cancel_iff (a := s)).mp
      rw [mul_inv_cancel_left, mul_neg, heq, neg_neg]
    simpa only [mul_inv_rev, inv_inv] using H.inv_mem hmem

/-- The central element belongs to every actual `Γ₀(N)`. -/
theorem gamma0_neg_one_mem (N : ℕ) :
    (-1 : SL(2, ℤ)) ∈ CongruenceSubgroup.Gamma0 N := by
  simp [CongruenceSubgroup.Gamma0_mem]

/-- Distinct actual `Γ₀(N)` charts cannot overlap on modular interiors,
even after applying a member of the subgroup. -/
theorem gamma0_interior_overlap_quotient_eq (N : ℕ)
    {r s γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma0 N)
    {z : UpperHalfPlane} (hr : r • z ∈ ModularGroup.fdo)
    (hs : s • (γ • z) ∈ ModularGroup.fdo) :
    (r : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N) = s :=
  modular_interior_overlap_quotient_eq _ (gamma0_neg_one_mem N) hγ hr hs

end ArtinMatthews
