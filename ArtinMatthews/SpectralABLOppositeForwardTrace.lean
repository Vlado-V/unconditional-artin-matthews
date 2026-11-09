module

public import ArtinMatthews.SpectralABLOppositeHeatTrace
public import ArtinMatthews.SpectralABLOppositeBareSpectrum


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set MeasureTheory Filter
open scoped MatrixGroups ContDiff Topology
noncomputable section

/-- The opposite-sign forward formula for a real compact spatial test,
with the source check transform and the exact native quarter factor. -/
theorem gamma0ABLOpposite_forward_trace_real (N : ℕ) [NeZero N] (r s : SL(2, ℤ))
    (hchart : r = s ∨ ¬ gamma0EisensteinCuspsEquivalent N r s)
    (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) (hmn : m*n < 0)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hp : tsupport f ⊆ Ioi (0 : ℝ)) (hr : ∀ x, star (f x) = f x) :
    let h := spectralABLOppositeEnergyTest f hf hc hp
    Summable (fun c : Ioi (0 : ℕ) => gamma0ABLOppositeGeometricTerm N r s c m n f) ∧
    Summable (fun i => ‖gamma0BareCuspidalTerm N h r s Y hY m n hm hn i‖) ∧
    IntegrableOn (gamma0BareContinuousRhoIntegrand N h r s Y hY m n hm hn) (Ioi (0 : ℝ)) ∧
    gamma0BareSourceSpectralSide N h r s Y hY m n hm hn =
      (1/(4*(Real.pi : ℂ)))*(∑' c : Ioi (0 : ℕ), gamma0ABLOppositeGeometricTerm N r s c m n f) := by
  let h := spectralABLOppositeEnergyTest f hf hc hp
  obtain ⟨hC,hI⟩ := gamma0OppositeBareSpectrum_integrable N r s Y hY m n hm hn f hf hc hp
  obtain ⟨hG,hLim⟩ := gamma0TrueWidthOppositeHeatSeries_tendsto N r s m n hm hn hmn f hf hc hp
  refine ⟨hG,hC,hI,?_⟩
  change gamma0BareSourceSpectralSide N h r s Y hY m n hm hn = _
  calc
    _ = (1/4 : ℂ)*((∑' c : Ioi (0 : ℕ), gamma0ABLOppositeGeometricTerm N r s c m n f)/
        (Real.pi : ℂ)) := by
      apply tendsto_nhds_unique (gamma0HeatSourceSpectralSide_tendsto_of_bare N h r s Y hY m n hm hn hC hI)
      apply (hLim.const_mul (1/4 : ℂ)).congr'
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
      exact (gamma0HeatOpposite_source_trace N r s hchart Y hY m n hm hn hmn f hf hc hp hr R hR).symm
    _ = _ := by field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero] <;> ring

end
end ArtinMatthews
