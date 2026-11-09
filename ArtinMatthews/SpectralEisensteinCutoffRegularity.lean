module

public import ArtinMatthews.SpectralEisensteinCutoffSmooth


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine smoothness and continuity of the locally finite noncompact
height cutoff of the actual source-cusp Eisenstein series. -/
noncomputable section
open Set Filter Topology
open scoped MatrixGroups ContDiff
namespace ArtinMatthews

theorem cuspEisensteinNormalizedHeight_continuous (N : ℕ) [NeZero N] (r a : SL(2,ℤ))
    (v : Gamma0CuspEisensteinRows N r a) : Continuous (cuspEisensteinNormalizedHeight N r a v) := by
  have hh : Continuous (cuspEisensteinRowHeight N r a v) := by
    change Continuous (fun z : UpperHalfPlane =>
      (Matrix.SpecialLinearGroup.mapGL ℝ (gamma0CuspEisensteinRowRepresentative N r a v).val • z).im)
    exact UpperHalfPlane.continuous_im.comp (continuous_const_smul _)
  exact hh.div_const _

theorem cuspEisensteinCutoffTerm_continuous (N : ℕ) [NeZero N] (r a : SL(2,ℤ))
    (s : ℂ) (hs : 1 < s.re) (v : Gamma0CuspEisensteinRows N r a) :
    Continuous (cuspEisensteinCutoffTerm N r a s v) := by
  have hh := eisensteinHeightCutoff_contDiff.continuous.comp
    (cuspEisensteinNormalizedHeight_continuous N r a v)
  have hc : Continuous (fun z : UpperHalfPlane =>
      (eisensteinHeightCutoff (cuspEisensteinNormalizedHeight N r a v z):ℂ)*
        ((gamma0CuspTrueWidth N a:ℂ)^(-s)*cuspEisensteinRowTerm N r a s v z)) :=
    (Complex.continuous_ofReal.comp hh).mul
      (continuous_const.mul (cuspEisensteinRowTerm_continuous N r a s hs v))
  convert! hc using 1
  funext z
  rw [cuspEisensteinCutoffTerm,cuspEisensteinNormalizedHeight_power]

theorem gamma0CuspEisensteinCutoff_continuous (N : ℕ) [NeZero N] (a : SL(2,ℤ))
    (s : ℂ) (hs : 1 < s.re) : Continuous (gamma0CuspEisensteinCutoff N a s) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  obtain ⟨T,hT⟩ := gamma0CuspEisensteinCutoff_locally_finite_sum N a s z
  have hc : Continuous (fun w : UpperHalfPlane => (1/2:ℂ)*
      ∑ v ∈ T, cuspEisensteinCutoffTerm N 1 a s v w) :=
    continuous_const.mul (continuous_finsetSum T (fun v _ => cuspEisensteinCutoffTerm_continuous N 1 a s hs v))
  exact hc.continuousAt.congr_of_eventuallyEq hT

theorem gamma0CuspEisensteinRemainder_continuous (N : ℕ) [NeZero N] (a : SL(2,ℤ))
    (s : ℂ) (hs : 1 < s.re) : Continuous (gamma0CuspEisensteinRemainder N a s) :=
  (gamma0CuspEisenstein_continuous N a s hs).sub (gamma0CuspEisensteinCutoff_continuous N a s hs)

theorem cuspEisensteinCutoffTerm_spatial_smooth (N : ℕ) [NeZero N] (r a : SL(2,ℤ))
    (s : ℂ) (v : Gamma0CuspEisensteinRows N r a) :
    ContDiffOn ℝ ∞ (fun z : ℂ => cuspEisensteinCutoffTerm N r a s v (UpperHalfPlane.ofComplex z))
      {z : ℂ | 0 < z.im} := by
  have hc := (cuspEisensteinCutoffPlaneTerm_smooth N r a s v).comp
    Complex.equivRealProdCLM.contDiff.contDiffOn
    (show MapsTo Complex.equivRealProdCLM {z : ℂ | 0 < z.im} {p : ℝ×ℝ | 0 < p.2} by
      intro z hz; exact hz)
  apply hc.congr
  intro z hz
  simp only [Function.comp_apply]
  rw [cuspEisensteinCutoffPlaneTerm_eq N r a s v (Complex.equivRealProdCLM z) hz,
    UpperHalfPlane.ofComplex_apply_of_im_pos hz]
  rfl

theorem gamma0CuspEisensteinCutoff_spatial_smooth (N : ℕ) [NeZero N] (a : SL(2,ℤ))
    (s : ℂ) : ContDiffOn ℝ ∞
      (fun z : ℂ => gamma0CuspEisensteinCutoff N a s (UpperHalfPlane.ofComplex z))
      {z : ℂ | 0 < z.im} := by
  intro z hz
  obtain ⟨T,hT⟩ := gamma0CuspEisensteinCutoff_locally_finite_sum N a s (UpperHalfPlane.ofComplex z)
  have hsource : z ∈ UpperHalfPlane.ofComplex.source := by
    simp only [UpperHalfPlane.ofComplex,OpenPartialHomeomorph.symm_source,
      Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target]
    exact ⟨⟨z,hz⟩,rfl⟩
  have he := hT.comp_tendsto (UpperHalfPlane.ofComplex.continuousAt hsource)
  have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hsmooth : ContDiffAt ℝ ∞ (fun w : ℂ => (1/2:ℂ)*
      ∑ v ∈ T, cuspEisensteinCutoffTerm N 1 a s v (UpperHalfPlane.ofComplex w)) z :=
    contDiffAt_const.mul (ContDiffAt.sum (fun v _ =>
      (cuspEisensteinCutoffTerm_spatial_smooth N 1 a s v).contDiffAt (hopen.mem_nhds hz)))
  exact (hsmooth.congr_of_eventuallyEq he).contDiffWithinAt

end ArtinMatthews
