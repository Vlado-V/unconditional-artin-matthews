module

public import ArtinMatthews.SpectralModularDensitySmoothGeometry
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine linear space of L² classes represented by smooth compact
seeds supported inside a prescribed upper-half-plane open set. -/
noncomputable section
open Set MeasureTheory Filter
open scoped CompactlySupported ContDiff
namespace ArtinMatthews

def h2SmoothSupportedLp (U : Set UpperHalfPlane) :
    Submodule ℂ (Lp ℂ 2 (volume.restrict U)) where
  carrier := {f | ∃ ψ : h2SmoothCompactSeeds, tsupport ψ.val ⊆ U ∧
    f =ᵐ[volume.restrict U] ψ.val}
  zero_mem' := by
    refine ⟨0, ?_, ?_⟩
    · change tsupport (fun _ : UpperHalfPlane => (0:ℂ)) ⊆ U
      simp
    · exact Lp.coeFn_zero ℂ 2 (volume.restrict U)
  add_mem' := by
    rintro f g ⟨ψ,hψ,hf⟩ ⟨φ,hφ,hg⟩
    refine ⟨ψ+φ, ?_, ?_⟩
    · exact (tsupport_add (ψ.val : UpperHalfPlane → ℂ) φ.val).trans (union_subset hψ hφ)
    · filter_upwards [Lp.coeFn_add f g,hf,hg] with z hz hfz hgz
      change (f+g) z = ψ.val z+φ.val z
      exact hz.trans (congrArg₂ (·+·) hfz hgz)
  smul_mem' := by
    rintro c f ⟨ψ,hψ,hf⟩
    refine ⟨c • ψ, ?_, ?_⟩
    · exact (tsupport_smul_subset_right (fun _ : UpperHalfPlane => c) ψ.val).trans hψ
    · filter_upwards [Lp.coeFn_smul c f,hf] with z hz hfz
      change (c • f) z = c • ψ.val z
      exact hz.trans (congrArg (c • ·) hfz)

theorem h2SmoothSupportedLp_mem (U : Set UpperHalfPlane) (ψ : h2SmoothCompactSeeds)
    (hψ : tsupport ψ.val ⊆ U) :
    (ψ.val.continuous.memLp_of_hasCompactSupport ψ.val.hasCompactSupport
      (p:=2) (μ:=volume.restrict U)).toLp ψ.val ∈ h2SmoothSupportedLp U :=
  ⟨ψ,hψ,MemLp.coeFn_toLp _⟩

end ArtinMatthews
