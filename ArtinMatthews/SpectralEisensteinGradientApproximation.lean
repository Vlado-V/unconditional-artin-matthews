module

public import ArtinMatthews.SpectralEisensteinRadialGradient
public import ArtinMatthews.SpectralEisensteinMassApproximation


set_option backward.privateInPublic true
@[expose] public section

/-! The literal gradient of each compact approximant is the constructed
energy gradient. The gradient series converges strongly in every L² chart. -/
noncomputable section
open Set Filter Topology MeasureTheory
open scoped MatrixGroups ContDiff
namespace ArtinMatthews

theorem gamma0CuspHeightProfileEnergy_gradient_ae (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hcf : HasCompactSupport f)
    (hpos : tsupport f ⊆ Ioi (0:ℝ)) (q : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :
    (gamma0EnergyGradient N (gamma0CuspHeightProfileEnergy N a f hf hcf hpos) q :
      UpperHalfPlane → EuclideanSpace ℂ (Fin 2)) =ᵐ[volume.restrict ModularGroup.fd]
        (fun z => h2SectionGradient (gamma0CuspHeightProfile N a f) (q.out⁻¹ • z)) := by
  let ψ := cuspHeightProfileSeed N a f hf hcf hpos
  let φ : h2SmoothCompactSeeds := (1/2:ℂ) • ψ
  have he : arithmeticPoincareSeed (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) φ.val=
      gamma0CuspHeightProfile N a f := by
    funext z
    change arithmeticPoincareSeed (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))
      ((1/2:ℂ) • ψ.val) z=_
    rw [arithmeticPoincareSeed_smul,gamma0CuspHeightProfile_eq_poincare N a f hf hcf hpos]
    rfl
  have h := arithmeticPoincareGradientRegionLp_coeFn
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) φ
    (Matrix.SpecialLinearGroup.mapGL ℝ q.out⁻¹)
  filter_upwards [h] with z hz
  change (arithmeticPoincareGradientRegionLp _ φ _ : UpperHalfPlane → EuclideanSpace ℂ (Fin 2)) z=_
  rw [hz,he]
  rfl

theorem gamma0CuspCompactProfile_gradient_memLp (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hcf : HasCompactSupport f)
    (hpos : tsupport f ⊆ Ioi (0:ℝ)) (q : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :
    MemLp (fun z => h2SectionGradient (gamma0CuspHeightProfile N a f) (q.out⁻¹ • z)) 2
      (volume.restrict ModularGroup.fd) :=
  (memLp_congr_ae (gamma0CuspHeightProfileEnergy_gradient_ae N a f hf hcf hpos q)).mp (Lp.memLp _)

theorem gamma0CuspRemainderGradientSeries_memLp (N : ℕ) [NeZero N] (a : SL(2,ℤ))
    (s : ℂ) (hs : 1 < s.re) (q : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :
    MemLp (fun z => gamma0CuspRemainderGradientSeries N a s (q.out⁻¹ • z)) 2
      (volume.restrict ModularGroup.fd) := by
  obtain ⟨M,hM,hbound⟩ := eisensteinHeightCutoff_weighted_deriv_bounded
  have hu (n : ℕ) := gamma0CuspCompactProfile_gradient_memLp N a _
    (eisensteinRadialApprox_smooth s (by positivity : (0:ℝ)<(n+1:ℕ)))
    (eisensteinRadialApprox_compact s (by positivity : (0:ℝ)<(n+1:ℕ)))
    (eisensteinRadialApprox_positive_support s (by positivity : (0:ℝ)<(n+1:ℕ))) q
  have hm : AEStronglyMeasurable (fun z => gamma0CuspRemainderGradientSeries N a s (q.out⁻¹ • z))
      (volume.restrict ModularGroup.fd) :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hu n).aestronglyMeasurable)
      (Filter.Eventually.of_forall (fun z => gamma0CuspRadialGradient_tendsto N a s hs (q.out⁻¹ • z)))
  apply ((gamma0CuspRadialEnvelope_memLp N a q.out s.re hs).const_mul (2*M+‖s‖)).mono' hm
  exact Filter.Eventually.of_forall (fun z => gamma0CuspRemainderGradientSeries_norm_le N a s hs hM hbound (q.out⁻¹ • z))

def gamma0CuspEisensteinRemainderGradientMass (N : ℕ) [NeZero N] (a : SL(2,ℤ))
    (s : ℂ) (hs : 1 < s.re) : Gamma0GradientL2 N :=
  WithLp.toLp 2 (fun q : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N =>
    (gamma0CuspRemainderGradientSeries_memLp N a s hs q).toLp _)

theorem gamma0CuspEisensteinRemainderGradientMass_ae (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (s : ℂ) (hs : 1 < s.re) (q : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :
    (gamma0CuspEisensteinRemainderGradientMass N a s hs q : UpperHalfPlane → EuclideanSpace ℂ (Fin 2))
      =ᵐ[volume.restrict ModularGroup.fd]
        (fun z => gamma0CuspRemainderGradientSeries N a s (q.out⁻¹ • z)) :=
  (gamma0CuspRemainderGradientSeries_memLp N a s hs q).coeFn_toLp

theorem gamma0CuspEisensteinApproxEnergy_gradient_chart_tendsto (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (s : ℂ) (hs : 1 < s.re) (q : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :
    Tendsto (fun n => gamma0EnergyGradient N (gamma0CuspEisensteinApproxEnergy N a s n) q)
      atTop (𝓝 (gamma0CuspEisensteinRemainderGradientMass N a s hs q)) := by
  obtain ⟨M,hM,hbound⟩ := eisensteinHeightCutoff_weighted_deriv_bounded
  let u (n : ℕ) (z : UpperHalfPlane) :=
    h2SectionGradient (gamma0CuspHeightProfile N a (eisensteinRadialApprox s (n+1:ℕ))) (q.out⁻¹ • z)
  let v (z : UpperHalfPlane) := gamma0CuspRemainderGradientSeries N a s (q.out⁻¹ • z)
  have hu (n : ℕ) : MemLp (u n) 2 (volume.restrict ModularGroup.fd) :=
    gamma0CuspCompactProfile_gradient_memLp N a _ (eisensteinRadialApprox_smooth s (by positivity))
      (eisensteinRadialApprox_compact s (by positivity)) (eisensteinRadialApprox_positive_support s (by positivity)) q
  have hv : MemLp v 2 (volume.restrict ModularGroup.fd) := gamma0CuspRemainderGradientSeries_memLp N a s hs q
  have h := spectralL2_toLp_dominated_convergence u v hu hv
    (fun z => (2*M+‖s‖)*gamma0CuspRadialEnvelope N a s.re (q.out⁻¹ • z))
    ((gamma0CuspRadialEnvelope_memLp N a q.out s.re hs).const_mul (2*M+‖s‖))
    (fun n => Filter.Eventually.of_forall (fun z => gamma0CuspRadialGradient_norm_le N a s hs
      (by positivity : (0:ℝ)<(n+1:ℕ)) hM hbound (q.out⁻¹ • z)))
    (Filter.Eventually.of_forall (fun z => gamma0CuspRemainderGradientSeries_norm_le N a s hs hM hbound (q.out⁻¹ • z)))
    (Filter.Eventually.of_forall (fun z => gamma0CuspRadialGradient_tendsto N a s hs (q.out⁻¹ • z)))
  have he (n : ℕ) : (hu n).toLp (u n)=gamma0EnergyGradient N (gamma0CuspEisensteinApproxEnergy N a s n) q := by
    apply Lp.ext
    exact (hu n).coeFn_toLp.trans (gamma0CuspHeightProfileEnergy_gradient_ae N a _ _ _ _ q).symm
  have he' : hv.toLp v=gamma0CuspEisensteinRemainderGradientMass N a s hs q := by
    apply Lp.ext
    exact hv.coeFn_toLp.trans (gamma0CuspEisensteinRemainderGradientMass_ae N a s hs q).symm
  simpa only [he,he'] using h

theorem gamma0CuspEisensteinApproxEnergy_gradient_tendsto (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (s : ℂ) (hs : 1 < s.re) :
    Tendsto (fun n => gamma0EnergyGradient N (gamma0CuspEisensteinApproxEnergy N a s n))
      atTop (𝓝 (gamma0CuspEisensteinRemainderGradientMass N a s hs)) := by
  have h : Tendsto (fun n => fun q => gamma0EnergyGradient N (gamma0CuspEisensteinApproxEnergy N a s n) q)
      atTop (𝓝 (fun q => gamma0CuspEisensteinRemainderGradientMass N a s hs q)) := by
    apply tendsto_pi_nhds.mpr
    intro q
    exact gamma0CuspEisensteinApproxEnergy_gradient_chart_tendsto N a s hs q
  simpa only [Function.comp_def,WithLp.toLp_ofLp] using
    (PiLp.continuous_toLp 2 _).continuousAt.tendsto.comp h

end ArtinMatthews
