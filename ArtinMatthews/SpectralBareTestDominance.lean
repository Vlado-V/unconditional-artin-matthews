module

public import ArtinMatthews.SpectralBareSpectrumLimit


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set MeasureTheory Filter
open scoped MatrixGroups Topology
noncomputable section

/-- Principal-symbol domination transfers the actual bare coefficient
bounds. The complementary cusp contribution is finite. -/
theorem gamma0BareSpectrum_of_symbol_dominance (N : ℕ) [NeZero N] (h h₀ : SpectralEnergyTest)
    (r s : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (C : ℝ) (hC : 0 ≤ C)
    (hP : ∀ i : Gamma0HeatPrincipalCuspidalIndex N,
      ‖gamma0CuspidalTestSymbol N h i.val‖ ≤ C*‖gamma0CuspidalTestSymbol N h₀ i.val‖)
    (hE : ∀ t : ℝ, ‖spectralContinuousTestSymbol h t‖ ≤ C*‖spectralContinuousTestSymbol h₀ t‖)
    (hS₀ : Summable (fun i => ‖gamma0BareCuspidalTerm N h₀ r s Y hY m n hm hn i‖))
    (hI₀ : IntegrableOn (gamma0BareContinuousRhoIntegrand N h₀ r s Y hY m n hm hn) (Ioi (0 : ℝ))) :
    Summable (fun i => ‖gamma0BareCuspidalTerm N h r s Y hY m n hm hn i‖) ∧
      IntegrableOn (gamma0BareContinuousRhoIntegrand N h r s Y hY m n hm hn) (Ioi (0 : ℝ)) := by
  have hP₀ := hS₀.subtype {i : Gamma0AllHeightSpectralIndex N |
    1/4 ≤ gamma0AllHeightGradientSpectralValue N i}
  have hP' : Summable (fun i : Gamma0HeatPrincipalCuspidalIndex N =>
      ‖gamma0BareCuspidalTerm N h r s Y hY m n hm hn i.val‖) := by
    apply (hP₀.mul_left C).of_nonneg_of_le (fun _ => norm_nonneg _)
    intro i
    let z := gamma0BareCuspidalAmplitude N i.val r Y hY m hm *
      star (gamma0BareCuspidalAmplitude N i.val s Y hY n hn)
    change ‖gamma0CuspidalTestSymbol N h i.val*z‖ ≤ C*‖gamma0CuspidalTestSymbol N h₀ i.val*z‖
    simp only [norm_mul]
    exact (mul_le_mul_of_nonneg_right (hP i) (norm_nonneg z)).trans_eq (by ring)
  refine ⟨gamma0HeatCuspidal_summable_of_principal N _ hP',?_⟩
  apply (hI₀.norm.const_mul C).mono'
    (gamma0BareContinuousRhoIntegrand_aestronglyMeasurable N h r s Y hY m n hm hn)
  filter_upwards with t
  let z := ∑ a : Gamma0EisensteinCuspClasses N, gamma0BareEisensteinSourceCoefficient N a r Y hY m hm t*
    star (gamma0BareEisensteinSourceCoefficient N a s Y hY n hn t)
  let q : ℂ := ((2*Real.pi : ℝ) : ℂ)
  change ‖(spectralContinuousTestSymbol h t/q)*z‖ ≤ C*‖(spectralContinuousTestSymbol h₀ t/q)*z‖
  simp only [norm_mul,norm_div]
  calc
    _ ≤ (C*‖spectralContinuousTestSymbol h₀ t‖/‖q‖)*‖z‖ :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (hE t) (norm_nonneg _)) (norm_nonneg _)
    _ = _ := by ring

theorem gamma0HeatSourceSpectralSide_tendsto_of_bare (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (r s : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (hS : Summable (fun i => ‖gamma0BareCuspidalTerm N h r s Y hY m n hm hn i‖))
    (hI : IntegrableOn (gamma0BareContinuousRhoIntegrand N h r s Y hY m n hm hn) (Ioi (0 : ℝ))) :
    Tendsto (fun R : ℝ => gamma0HeatSourceSpectralSide N h r s Y hY m n hm hn R) atTop
      (𝓝 (gamma0BareSourceSpectralSide N h r s Y hY m n hm hn)) := by
  let F := gamma0BareCuspidalTerm N h r s Y hY m n hm hn
  have hCuspidal : Tendsto (fun R : ℝ =>
      ∑' i, gamma0HeatCuspidalTerm N h r s Y hY m n hm hn R i) atTop (𝓝 (∑' i, F i)) := by
    apply tendsto_tsum_of_dominated_convergence (hS.mul_left (Real.exp (1/2 : ℝ)))
    · intro i
      simpa only [gamma0HeatCuspidalTerm,mul_one,F] using
        (spectralHeatEnergyWeight_tendsto (gamma0AllHeightGradientSpectralValue N i)).const_mul (F i)
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
      exact fun i => gamma0HeatCuspidalTerm_norm_le N h r s Y hY m n hm hn hR i
  have hContinuous := gamma0HeatContinuousRhoIntegral_tendsto_bare N h r s Y hY m n hm hn hI
  have hResidual := gamma0HeatResidualRhoSum_tendsto_bare N h r s m n hm hn
  simpa only [F,gamma0HeatSourceSpectralSide_split,gamma0BareSourceSpectralSide] using
    hCuspidal.add (hContinuous.add hResidual)

end
end ArtinMatthews
