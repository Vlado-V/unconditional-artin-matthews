module

public import ArtinMatthews.SpectralEisensteinCompactExponential
public import ArtinMatthews.SpectralEisensteinOutgoingCharts
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions


set_option backward.privateInPublic true
@[expose] public section

/-! The actual source-height cutoff is entire in the literal L² norm of
each compact chart, using the same finite row set for every parameter. -/
noncomputable section
open Set Filter Topology MeasureTheory
open scoped MatrixGroups BoundedContinuousFunction
namespace ArtinMatthews

theorem spectralContinuous_memLp_compactRegion (F : UpperHalfPlane → ℂ) (hF : Continuous F)
    (K : Set UpperHalfPlane) (hK : IsCompact K) : MemLp F 2 (volume.restrict K) :=
  (memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).mpr
    ((hF.norm.pow 2).continuousOn.integrableOn_compact hK)

theorem gamma0CuspEisensteinCutoff_chart_continuous (N : ℕ) [NeZero N] (a r : SL(2,ℤ)) (s : ℂ) :
    Continuous (fun z : UpperHalfPlane => gamma0CuspEisensteinCutoff N a s (r⁻¹ • z)) := by
  change Continuous (fun z : UpperHalfPlane => gamma0CuspEisensteinCutoff N a s
    (Matrix.SpecialLinearGroup.mapGL ℝ r⁻¹ • z))
  exact (gamma0CuspOutgoingCutoff_continuous N a s).comp (continuous_const_smul _)

def gamma0CuspEisensteinCutoffCompactMass (N : ℕ) [NeZero N] (a r : SL(2,ℤ))
    (K : Set UpperHalfPlane) (hK : IsCompact K) (s : ℂ) : Lp ℂ 2 (volume.restrict K) :=
  (spectralContinuous_memLp_compactRegion _ (gamma0CuspEisensteinCutoff_chart_continuous N a r s) K hK).toLp _

theorem gamma0CuspEisensteinCutoffCompactMass_ae (N : ℕ) [NeZero N] (a r : SL(2,ℤ))
    (K : Set UpperHalfPlane) (hK : IsCompact K) (s : ℂ) :
    gamma0CuspEisensteinCutoffCompactMass N a r K hK s =ᵐ[volume.restrict K]
      fun z => gamma0CuspEisensteinCutoff N a s (r⁻¹ • z) :=
  (spectralContinuous_memLp_compactRegion _ (gamma0CuspEisensteinCutoff_chart_continuous N a r s) K hK).coeFn_toLp

theorem gamma0CuspEisensteinCutoffCompactMass_analyticAt (N : ℕ) [NeZero N]
    (a r : SL(2,ℤ)) (K : Set UpperHalfPlane) (hK : IsCompact K) (s : ℂ) :
    AnalyticAt ℂ (gamma0CuspEisensteinCutoffCompactMass N a r K hK) s := by
  classical
  let G (z : UpperHalfPlane) := r⁻¹ • z
  have hG : Continuous G := by
    change Continuous (fun z : UpperHalfPlane => Matrix.SpecialLinearGroup.mapGL ℝ r⁻¹ • z)
    exact continuous_const_smul _
  let H (v : Gamma0CuspEisensteinRows N 1 a) (z : UpperHalfPlane) :=
    cuspEisensteinNormalizedHeight N 1 a v (G z)
  have hH (v) : Continuous (H v) := (cuspEisensteinNormalizedHeight_continuous N 1 a v).comp hG
  have hp (v) (z : UpperHalfPlane) : 0<H v z := cuspEisensteinNormalizedHeight_pos N 1 a v (G z)
  have hfin := cuspEisensteinHeight_compact_finite N 1 a zero_lt_one (hK.image hG)
  let T := hfin.toFinset
  have hbound (v : Gamma0CuspEisensteinRows N 1 a) : ∃ M : ℝ, 1≤M ∧ ∀ z∈K,H v z≤M := by
    obtain ⟨M,hM⟩ := hK.exists_bound_of_continuousOn (hH v).continuousOn
    refine ⟨max 1 M,le_max_left _ _,fun z hz => ?_⟩
    exact ((le_abs_self (H v z)).trans (by simpa only [Real.norm_eq_abs] using hM z hz)).trans
      (le_max_right _ _)
  choose M hM hbound using hbound
  let B (w : ℂ) : UpperHalfPlane →ᵇ ℂ :=
    (1/2:ℂ) • ∑ v ∈ T, spectralCompactCutoffExponential (H v) (hH v) (hp v) (M v) (hM v) w
  have hB' : AnalyticAt ℂ (fun w : ℂ => ∑ v ∈ T,
      spectralCompactCutoffExponential (H v) (hH v) (hp v) (M v) (hM v) w) s :=
    T.analyticAt_fun_sum (fun v _ => spectralCompactCutoffExponential_analyticAt (H v) (hH v) (hp v) (M v) (hM v) s)
  have hB : AnalyticAt ℂ B s :=
    (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (1/2:ℂ)) s).smul hB' 
  have hpoint (w : ℂ) (z : UpperHalfPlane) (hz : z∈K) :
      B w z=gamma0CuspEisensteinCutoff N a w (G z) := by
    rw [gamma0CuspEisensteinCutoff_eq_profile,
      gamma0CuspHeightProfile_eq_tsum N a _ zero_lt_one (fun _ ht => eisensteinVerticalCutoffMode_zero w ht)]
    simp only [B,BoundedContinuousFunction.smul_apply,smul_eq_mul,BoundedContinuousFunction.sum_apply]
    congr 1
    rw [tsum_eq_sum (s := T)]
    · apply Finset.sum_congr rfl
      intro v _
      exact spectralCompactCutoffExponential_eq _ _ _ _ _ w z (hbound v z hz)
    · intro v hv
      apply eisensteinVerticalCutoffMode_zero
      by_contra hn
      exact hv (hfin.mem_toFinset.mpr ⟨G z,⟨z,hz,rfl⟩,(lt_of_not_ge hn).le⟩)
  let _ : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hK.measure_lt_top (μ := volume)⟩
  let L : (UpperHalfPlane →ᵇ ℂ) →L[ℂ] Lp ℂ 2 (volume.restrict K) :=
    BoundedContinuousFunction.toLp 2 (volume.restrict K) ℂ
  have he (w : ℂ) : gamma0CuspEisensteinCutoffCompactMass N a r K hK w=L (B w) := by
    apply Lp.ext
    filter_upwards [gamma0CuspEisensteinCutoffCompactMass_ae N a r K hK w,
      BoundedContinuousFunction.coeFn_toLp 2 (volume.restrict K) ℂ (B w),
      ae_restrict_mem hK.isClosed.measurableSet] with z hC hL hz
    exact hC.trans ((hpoint w z hz).symm.trans hL.symm)
  rw [funext he]
  exact (L.analyticAt _).comp hB

end ArtinMatthews
