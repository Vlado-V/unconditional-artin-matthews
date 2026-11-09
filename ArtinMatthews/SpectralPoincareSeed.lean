module

public import Mathlib.NumberTheory.ModularForms.ProperlyDiscontinuous
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.Topology.ContinuousMap.CompactlySupported


set_option backward.privateInPublic true
@[expose] public section

/-!
Actual compact-seed periodization for arithmetic subgroups acting on H².
Proper discontinuity and compactness give local finiteness; hence these are
constructed continuous automorphic functions, with no convergence assumption.
The local-finiteness argument is the dimension-independent one used by
math-main's CubicThetaPoincareSections, here applied to the actual H² action.
-/

noncomputable section
open Set Filter Topology
open scoped BigOperators CompactlySupported MatrixGroups Pointwise

namespace ArtinMatthews

variable (𝒢 : Subgroup (GL (Fin 2) ℝ)) [𝒢.IsArithmetic]

theorem arithmetic_compact_translates_locallyFinite {K : Set UpperHalfPlane}
    (hK : IsCompact K) :
    LocallyFinite (fun g : 𝒢 => (fun z : UpperHalfPlane => g • z) ⁻¹' K) := by
  intro z
  obtain ⟨L, hL, hz⟩ := exists_compact_mem_nhds z
  refine ⟨L, hz, ?_⟩
  apply (finite_disjoint_inter_image (Γ := 𝒢) hL hK).subset
  rintro g ⟨p, hp, hpL⟩
  exact ⟨g • p, ⟨p, hpL, rfl⟩, hp⟩

theorem arithmetic_poincare_support_locallyFinite (ψ : C_c(UpperHalfPlane, ℂ)) :
    LocallyFinite (fun g : 𝒢 => Function.support (fun z : UpperHalfPlane => ψ (g • z))) := by
  apply (arithmetic_compact_translates_locallyFinite 𝒢 ψ.hasCompactSupport).subset
  intro g z hz
  exact subset_tsupport ψ hz

/-- The actual locally finite arithmetic periodization of a compact seed. -/
def arithmeticPoincareSeed (ψ : C_c(UpperHalfPlane, ℂ)) : C(UpperHalfPlane, ℂ) :=
  ⟨fun z => ∑ᶠ g : 𝒢, ψ (g • z),
    continuous_finsum (fun g => ψ.continuous.comp (continuous_const_smul g))
      (arithmetic_poincare_support_locallyFinite 𝒢 ψ)⟩

theorem arithmeticPoincareSeed_invariant (ψ : C_c(UpperHalfPlane, ℂ))
    (h : 𝒢) (z : UpperHalfPlane) :
    arithmeticPoincareSeed 𝒢 ψ (h • z) = arithmeticPoincareSeed 𝒢 ψ z := by
  change (∑ᶠ g : 𝒢, ψ (g • (h • z))) = ∑ᶠ g : 𝒢, ψ (g • z)
  simp_rw [← mul_smul]
  exact finsum_comp_equiv (f := fun g : 𝒢 => ψ (g • z)) (Equiv.mulRight h)

/-- Every nonzero periodized value has a representative in the actual compact
support of the seed.  Thus compactness modulo the group is proved from the
construction, not postulated. -/
theorem arithmeticPoincareSeed_support (ψ : C_c(UpperHalfPlane, ℂ))
    {z : UpperHalfPlane} (hz : arithmeticPoincareSeed 𝒢 ψ z ≠ 0) :
    ∃ g : 𝒢, g • z ∈ tsupport ψ := by
  by_contra! h
  apply hz
  change (∑ᶠ g : 𝒢, ψ (g • z)) = 0
  have hzero (g : 𝒢) : ψ (g • z) = 0 := image_eq_zero_of_notMem_tsupport (h g)
  simp only [hzero, finsum_zero]

/-- At every point the periodization agrees on a neighborhood with an actual
finite sum.  This is the form needed for differentiating smooth seeds. -/
theorem arithmeticPoincareSeed_locally_finite_sum (ψ : C_c(UpperHalfPlane, ℂ))
    (z : UpperHalfPlane) :
    ∃ s : Finset 𝒢, (arithmeticPoincareSeed 𝒢 ψ : UpperHalfPlane → ℂ) =ᶠ[𝓝 z]
      (fun y => ∑ g ∈ s, ψ (g • y)) := by
  classical
  obtain ⟨t, ht, hfinite⟩ := arithmetic_poincare_support_locallyFinite 𝒢 ψ z
  refine ⟨hfinite.toFinset, ?_⟩
  filter_upwards [ht] with y hy
  apply finsum_eq_sum_of_support_subset
  intro g hg
  exact hfinite.mem_toFinset.mpr ⟨y, hg, hy⟩

end ArtinMatthews
