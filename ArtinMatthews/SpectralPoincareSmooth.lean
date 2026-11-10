module

public import ArtinMatthews.SpectralPoincareSeed
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal


set_option backward.privateInPublic true
@[expose] public section

/-! Real smoothness of the constructed H² arithmetic periodizations. -/

noncomputable section
open Set Filter Topology
open scoped BigOperators CompactlySupported MatrixGroups ContDiff

namespace ArtinMatthews

private def h2Mobius (g : GL (Fin 2) ℝ) (z : ℂ) : ℂ :=
  UpperHalfPlane.num g z / UpperHalfPlane.denom g z

private theorem h2Mobius_smoothAt (g : GL (Fin 2) ℝ) {z : ℂ} (hz : 0 < z.im) :
    ContDiffAt ℝ ∞ (h2Mobius g) z := by
  have hden : UpperHalfPlane.denom g z ≠ 0 := UpperHalfPlane.denom_ne_zero g ⟨z, hz⟩
  have hc : ContDiffAt ℂ ∞ (h2Mobius g) z := by
    unfold h2Mobius UpperHalfPlane.num UpperHalfPlane.denom
    fun_prop (disch := exact hden)
  exact hc.restrict_scalars ℝ

private theorem h2Mobius_positive (g : GL (Fin 2) ℝ) (hg : 0 < g.det.val)
    {z : ℂ} (hz : 0 < z.im) : 0 < (h2Mobius g z).im := by
  have h := (g • (⟨z, hz⟩ : UpperHalfPlane)).im_pos
  rw [← UpperHalfPlane.coe_im, UpperHalfPlane.coe_smul_of_det_pos hg] at h
  exact h

private theorem h2Mobius_ofComplex (g : GL (Fin 2) ℝ) (hg : 0 < g.det.val)
    {z : ℂ} (hz : 0 < z.im) :
    UpperHalfPlane.ofComplex (h2Mobius g z) = g • UpperHalfPlane.ofComplex z := by
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz]
  have h : h2Mobius g z = ((g • (⟨z, hz⟩ : UpperHalfPlane) : UpperHalfPlane) : ℂ) :=
    by simpa only [h2Mobius] using
      (UpperHalfPlane.coe_smul_of_det_pos hg (⟨z, hz⟩ : UpperHalfPlane)).symm
  rw [h, UpperHalfPlane.ofComplex_apply]

variable (𝒢 : Subgroup (GL (Fin 2) ℝ)) [𝒢.IsArithmetic] [𝒢.HasDetOne]

omit [𝒢.IsArithmetic] in
private theorem arithmetic_poincare_term_smooth (ψ : C_c(UpperHalfPlane, ℂ))
    (hψ : ContDiffOn ℝ ∞ (fun z : ℂ => ψ (UpperHalfPlane.ofComplex z))
      {z : ℂ | 0 < z.im}) (g : 𝒢) {z : ℂ} (hz : 0 < z.im) :
    ContDiffAt ℝ ∞ (fun z : ℂ => ψ (g • UpperHalfPlane.ofComplex z)) z := by
  have hg : 0 < (g : GL (Fin 2) ℝ).det.val := by
    rw [Subgroup.HasDetOne.det_eq g.property]
    exact zero_lt_one
  have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hbase := hψ.contDiffAt (hopen.mem_nhds (h2Mobius_positive g hg hz))
  have hcomp := hbase.comp z (h2Mobius_smoothAt g hz)
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [hopen.mem_nhds hz] with x hx
  change ψ (g • UpperHalfPlane.ofComplex x) = ψ (UpperHalfPlane.ofComplex (h2Mobius g x))
  rw [h2Mobius_ofComplex g hg hx]
  rfl

/-- A genuine compact smooth seed gives a genuine smooth automorphic
periodization.  Local finiteness is proved, rather than assumed. -/
theorem arithmeticPoincareSeed_smooth (ψ : C_c(UpperHalfPlane, ℂ))
    (hψ : ContDiffOn ℝ ∞ (fun z : ℂ => ψ (UpperHalfPlane.ofComplex z))
      {z : ℂ | 0 < z.im}) :
    ContDiffOn ℝ ∞
      (fun z : ℂ => arithmeticPoincareSeed 𝒢 ψ (UpperHalfPlane.ofComplex z))
      {z : ℂ | 0 < z.im} := by
  intro z hz
  obtain ⟨s, hs⟩ := arithmeticPoincareSeed_locally_finite_sum 𝒢 ψ
    (UpperHalfPlane.ofComplex z)
  have hzsource : z ∈ UpperHalfPlane.ofComplex.source := by
    simp only [UpperHalfPlane.ofComplex, OpenPartialHomeomorph.symm_source,
      Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target]
    exact ⟨⟨z, hz⟩, rfl⟩
  have he := hs.comp_tendsto (UpperHalfPlane.ofComplex.continuousAt hzsource)
  have hfinite : ContDiffAt ℝ ∞
      (fun x : ℂ => ∑ g ∈ s, ψ (g • UpperHalfPlane.ofComplex x)) z :=
    ContDiffAt.sum (fun g _ => arithmetic_poincare_term_smooth 𝒢 ψ hψ g hz)
  exact (hfinite.congr_of_eventuallyEq he).contDiffWithinAt

end ArtinMatthews
