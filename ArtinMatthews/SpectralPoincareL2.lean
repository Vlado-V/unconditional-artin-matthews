module

public import ArtinMatthews.SpectralPoincareGamma0
public import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
public import Mathlib.NumberTheory.Modular
public import ArtinMatthews.SpectralHyperbolicFiniteVolume
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan


set_option backward.privateInPublic true
@[expose] public section

/-! Actual L² realization of compact-seed arithmetic periodizations on the
standard modular region and its translates. -/

noncomputable section
open Set MeasureTheory Filter
open scoped CompactlySupported MatrixGroups

namespace ArtinMatthews

variable (𝒢 : Subgroup (GL (Fin 2) ℝ)) [𝒢.IsArithmetic]

/-- Compactness modulo the group and actual invariance give a global bound. -/
theorem arithmeticPoincareSeed_global_bound (ψ : C_c(UpperHalfPlane, ℂ)) :
    ∃ C > 0, ∀ z, ‖arithmeticPoincareSeed 𝒢 ψ z‖ ≤ C := by
  obtain ⟨C, hC⟩ := ψ.hasCompactSupport.exists_bound_of_continuousOn
    (arithmeticPoincareSeed 𝒢 ψ).continuous.continuousOn
  refine ⟨max C 1, by positivity, fun z => ?_⟩
  by_cases hz : arithmeticPoincareSeed 𝒢 ψ z = 0
  · simp only [hz, norm_zero]
    positivity
  obtain ⟨g, hg⟩ := arithmeticPoincareSeed_support 𝒢 ψ hz
  calc
    ‖arithmeticPoincareSeed 𝒢 ψ z‖ = ‖arithmeticPoincareSeed 𝒢 ψ (g • z)‖ := by
      rw [arithmeticPoincareSeed_invariant]
    _ ≤ C := hC _ hg
    _ ≤ max C 1 := le_max_left _ _

instance modularRegion_finiteMeasure :
    IsFiniteMeasure ((volume : Measure UpperHalfPlane).restrict ModularGroup.fd) :=
  ⟨by simpa only [Measure.restrict_apply_univ] using modular_fundamental_region_volume_lt_top⟩

/-- Square-integrability on every actual translate of the standard region. -/
theorem arithmeticPoincareSeed_memLp_modularRegion (ψ : C_c(UpperHalfPlane, ℂ))
    (r : GL (Fin 2) ℝ) :
    MemLp (fun z : UpperHalfPlane => arithmeticPoincareSeed 𝒢 ψ (r • z)) 2
      (volume.restrict ModularGroup.fd) := by
  obtain ⟨C, _, hC⟩ := arithmeticPoincareSeed_global_bound 𝒢 ψ
  apply MemLp.of_bound
    ((arithmeticPoincareSeed 𝒢 ψ).continuous.comp (continuous_const_smul r)).aestronglyMeasurable C
  exact Eventually.of_forall (fun z => hC (r • z))

/-- The actual region L² vector, not an assumed square-integrable proxy. -/
def arithmeticPoincareRegionLp (ψ : C_c(UpperHalfPlane, ℂ)) (r : GL (Fin 2) ℝ) :
    Lp ℂ 2 (volume.restrict ModularGroup.fd) :=
  (arithmeticPoincareSeed_memLp_modularRegion 𝒢 ψ r).toLp _

theorem arithmeticPoincareRegionLp_coeFn (ψ : C_c(UpperHalfPlane, ℂ))
    (r : GL (Fin 2) ℝ) :
    (arithmeticPoincareRegionLp 𝒢 ψ r : UpperHalfPlane → ℂ) =ᵐ[volume.restrict ModularGroup.fd]
      (fun z => arithmeticPoincareSeed 𝒢 ψ (r • z)) :=
  (arithmeticPoincareSeed_memLp_modularRegion 𝒢 ψ r).coeFn_toLp

/-- Actual Γ₀(N) core square-integrability, with arithmeticity discharged. -/
theorem gamma0PoincareSeed_memLp_modularRegion (N : ℕ) [NeZero N]
    (ψ : C_c(UpperHalfPlane, ℂ)) (r : SL(2, ℤ)) :
    MemLp (fun z : UpperHalfPlane => gamma0PoincareSeed N ψ (r • z)) 2
      (volume.restrict ModularGroup.fd) :=
  arithmeticPoincareSeed_memLp_modularRegion _ ψ (Matrix.SpecialLinearGroup.mapGL ℝ r)

end ArtinMatthews
