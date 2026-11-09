module

public import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
public import Mathlib.Tactic


set_option backward.privateInPublic true
@[expose] public section

/-! The actual compact Fredholm alternative for the mass-form pencil.
Invertibility is proved off its genuine kernel parameters. -/
noncomputable section
namespace ArtinMatthews
open Module

section
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

omit [CompleteSpace V] in
def spectralCompactFormPencil (T : V →L[ℂ] V) (z : ℂ) : V →L[ℂ] V :=
  ContinuousLinearMap.id ℂ V-(z+1) • T

theorem spectralCompactFormPencil_isUnit_iff (T : V →L[ℂ] V) (hT : IsCompactOperator T)
    (z : ℂ) : IsUnit (spectralCompactFormPencil T z) ↔
      ∀ u : V, spectralCompactFormPencil T z u=0 → u=0 := by
  constructor
  · intro h u hu
    apply ((ContinuousLinearMap.isUnit_iff_bijective.mp h).1)
    rwa [map_zero]
  · intro hk
    by_cases hz : z+1=0
    · rw [spectralCompactFormPencil,hz,zero_smul,sub_zero]
      exact isUnit_one
    let μ : ℂ := (z+1)⁻¹
    have hμ : μ≠0 := inv_ne_zero hz
    have hR := (hT.hasEigenvalue_or_mem_resolventSet hμ).resolve_left (fun hE => by
      obtain ⟨u,hu⟩ := hE.exists_hasEigenvector
      have he : T u=μ • u := Module.End.mem_eigenspace_iff.mp hu.1
      have hzero : spectralCompactFormPencil T z u=0 := by
        change u-(z+1) • T u=0
        rw [he,smul_smul,show (z+1)*μ=1 from mul_inv_cancel₀ hz,one_smul,sub_self]
      exact hu.2 (hk u hzero))
    have he : algebraMap ℂ (V →L[ℂ] V) (z+1)*
        (algebraMap ℂ (V →L[ℂ] V) μ-T)=spectralCompactFormPencil T z := by
      ext u
      change (z+1) • (μ • u-T u)=u-(z+1) • T u
      rw [smul_sub,smul_smul,show (z+1)*μ=1 from mul_inv_cancel₀ hz,one_smul]
    rw [← he]
    exact ((isUnit_iff_ne_zero.mpr hz).map (algebraMap ℂ (V →L[ℂ] V))).mul
      (spectrum.mem_resolventSet_iff.mp hR)

end
end ArtinMatthews
