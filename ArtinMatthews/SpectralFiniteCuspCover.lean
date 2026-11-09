module

public import Mathlib.NumberTheory.Modular
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.GroupTheory.Index
public import Mathlib.Analysis.Complex.UpperHalfPlane.Topology


set_option backward.privateInPublic true
@[expose] public section

/-!
A finite-index subgroup inherits a compact core and finitely many cusp charts
from the existing modular fundamental region.  This is a geometric cover, not
an assertion of disjointness for the ineffective SL₂ action.
-/

noncomputable section
open Set
open scoped MatrixGroups Pointwise

namespace ArtinMatthews

/-- Finite-index automorphic reduction to a compact core or a bounded-width
cusp.  All representatives and the core are constructed from the actual
finite coset space and Mathlib's modular fundamental region. -/
theorem finiteIndex_compact_core_cusp_cover (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (Y : ℝ) :
    ∃ s : Finset SL(2, ℤ), ∃ K : Set UpperHalfPlane, s.card ≤ Γ.index ∧ IsCompact K ∧
      ∀ τ : UpperHalfPlane, ∃ γ : Γ,
        (γ : SL(2, ℤ)) • τ ∈ K ∨
        ∃ r ∈ s, ∃ z : UpperHalfPlane,
          |z.re| ≤ (1 : ℝ) / 2 ∧ Y < z.im ∧
            (γ : SL(2, ℤ)) • τ = r⁻¹ • z := by
  classical
  let : Fintype (SL(2, ℤ) ⧸ Γ) := Fintype.ofFinite _
  let s : Finset SL(2, ℤ) := Finset.univ.image
    (fun q : SL(2, ℤ) ⧸ Γ => q.out)
  let K : Set UpperHalfPlane := ⋃ r ∈ s,
    (r⁻¹ : SL(2, ℤ)) • ModularGroup.truncatedFundamentalDomain Y
  refine ⟨s, K, ?_, ?_, ?_⟩
  · exact (Finset.card_image_le).trans_eq (by
      simp [Subgroup.index, Nat.card_eq_fintype_card])
  · apply Set.Finite.isCompact_biUnion s.finite_toSet
    intro r _
    have hc : Continuous (fun z : UpperHalfPlane => (r⁻¹ : SL(2, ℤ)) • z) := by
      change Continuous (fun z : UpperHalfPlane =>
        Matrix.SpecialLinearGroup.mapGL ℝ (r⁻¹ : SL(2, ℤ)) • z)
      exact continuous_const_smul _
    exact (ModularGroup.isCompact_truncatedFundamentalDomain Y).image
      hc
  · intro τ
    obtain ⟨δ, hδ⟩ := ModularGroup.exists_smul_mem_fd τ
    let r : SL(2, ℤ) := (QuotientGroup.mk δ : SL(2, ℤ) ⧸ Γ).out
    have hr : r ∈ s := Finset.mem_image.mpr
      ⟨QuotientGroup.mk δ, Finset.mem_univ _, rfl⟩
    have hγ : r⁻¹ * δ ∈ Γ := QuotientGroup.eq.mp (Quotient.out_eq' _)
    refine ⟨⟨r⁻¹ * δ, hγ⟩, ?_⟩
    by_cases hheight : (δ • τ).im ≤ Y
    · left
      apply Set.mem_iUnion₂.mpr
      refine ⟨r, hr, ?_⟩
      exact ⟨δ • τ, ⟨hδ, hheight⟩, (mul_smul r⁻¹ δ τ).symm⟩
    · right
      exact ⟨r, hr, δ • τ, hδ.2, lt_of_not_ge hheight, mul_smul r⁻¹ δ τ⟩

/-- The actual congruence groups in Kuznetsov inherit the constructed cover;
finiteness of their index is a theorem of Mathlib. -/
theorem gamma0_compact_core_cusp_cover (N : ℕ) [NeZero N] (Y : ℝ) :
    ∃ s : Finset SL(2, ℤ), ∃ K : Set UpperHalfPlane,
      s.card ≤ (CongruenceSubgroup.Gamma0 N).index ∧ IsCompact K ∧
      ∀ τ : UpperHalfPlane, ∃ γ : CongruenceSubgroup.Gamma0 N,
        (γ : SL(2, ℤ)) • τ ∈ K ∨
        ∃ r ∈ s, ∃ z : UpperHalfPlane,
          |z.re| ≤ (1 : ℝ) / 2 ∧ Y < z.im ∧
            (γ : SL(2, ℤ)) • τ = r⁻¹ • z :=
  finiteIndex_compact_core_cusp_cover (CongruenceSubgroup.Gamma0 N) Y

end ArtinMatthews
