module

public import ArtinMatthews.SpectralHeatCuspidalBareLimit
public import ArtinMatthews.SpectralBareDiagonalBounds
public import ArtinMatthews.SpectralBareWindowPositivity
public import ArtinMatthews.SpectralABLModulusLimit


set_option backward.privateInPublic true
@[expose] public section

/-! Actual bare source spectral convergence in all three sectors.
The two Gaussian diagonal bounds come from the checked geometry. -/

noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups Topology
namespace ArtinMatthews

theorem spectralHeatScale_nat_tendsto_atTop :
    Tendsto (fun k : ℕ => (k : ℝ)+1) atTop atTop := by
  apply tendsto_atTop.2
  intro x
  obtain ⟨k,hk⟩ := exists_nat_ge x
  filter_upwards [eventually_ge_atTop k] with j hj
  have hj' : (k : ℝ) ≤ j := by exact_mod_cast hj
  linarith

def gamma0BareSourceSpectralSide (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (r s : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) : ℂ :=
  (∑' i, gamma0BareCuspidalTerm N h r s Y hY m n hm hn i)+
    ((∫ t in Ioi (0 : ℝ), gamma0BareContinuousRhoIntegrand N h r s Y hY m n hm hn t)+
      gamma0BareResidualRhoSum N h r s m n hm hn)

theorem gamma0HeatSourceSpectralSide_tendsto_bare (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (r s : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (hCusp : ∀ i : Gamma0HeatPrincipalCuspidalIndex N,
      ‖gamma0CuspidalTestSymbol N h i.val‖ = (gamma0CuspidalTestSymbol N h i.val).re)
    (hReal : ∀ t : ℝ, ((spectralContinuousTestSymbol h t).re : ℂ) = spectralContinuousTestSymbol h t)
    (hNorm : ∀ t : ℝ, ‖spectralContinuousTestSymbol h t‖ = (spectralContinuousTestSymbol h t).re)
    (hr : ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 1 ≤ R →
      ‖gamma0HeatSourceSpectralSide N h r r Y hY m m hm hm R‖ ≤ C)
    (hs : ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 1 ≤ R →
      ‖gamma0HeatSourceSpectralSide N h s s Y hY n n hn hn R‖ ≤ C) :
    Summable (fun i => ‖gamma0BareCuspidalTerm N h r s Y hY m n hm hn i‖) ∧
      IntegrableOn (gamma0BareContinuousRhoIntegrand N h r s Y hY m n hm hn) (Ioi (0 : ℝ)) ∧
      Tendsto (fun k : ℕ => gamma0HeatSourceSpectralSide N h r s Y hY m n hm hn ((k : ℝ)+1))
        atTop (𝓝 (gamma0BareSourceSpectralSide N h r s Y hY m n hm hn)) := by
  have hPos (t : ℝ) : 0 ≤ (spectralContinuousTestSymbol h t).re := (hNorm t) ▸ norm_nonneg _
  obtain ⟨Cr,hCr,hr⟩ := hr
  obtain ⟨Cs,hCs,hs⟩ := hs
  obtain ⟨Dr,_,hrD,hrI⟩ := gamma0HeatSpectrum_diagonal_bounds N h r Y hY m hm hCusp hReal hPos Cr hCr hr
  obtain ⟨Ds,_,hsD,hsI⟩ := gamma0HeatSpectrum_diagonal_bounds N h s Y hY n hn hCusp hReal hPos Cs hCs hs
  obtain ⟨_,hSum,hCuspLimit⟩ := gamma0HeatCuspidal_tendsto_bare N h r s Y hY m n hm hn hCusp Dr Ds hrD hsD
  have hrL := (gamma0BareContinuousRhoDiagonal_integrable N h r Y hY m hm hReal hPos Dr hrI).1
  have hsL := (gamma0BareContinuousRhoDiagonal_integrable N h s Y hY n hn hReal hPos Ds hsI).1
  have hI := gamma0BareContinuousRhoIntegrand_integrable N h r s Y hY m n hm hn hNorm hrL hsL
  have hILimit := (gamma0HeatContinuousRhoIntegral_tendsto_bare N h r s Y hY m n hm hn hI).comp
    spectralHeatScale_nat_tendsto_atTop
  have hResidual := (gamma0HeatResidualRhoSum_tendsto_bare N h r s m n hm hn).comp
    spectralHeatScale_nat_tendsto_atTop
  refine ⟨hSum,hI,?_⟩
  simpa only [Function.comp_def,gamma0HeatSourceSpectralSide_split,gamma0BareSourceSpectralSide] using
    hCuspLimit.add (hILimit.add hResidual)

theorem gamma0HeatRegular_source_tendsto_bare (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (T ε : ℝ) (hT : 0 < T) :
    let h := spectralABLRegularEnergyTest T (T^(1-ε)) hT (Real.rpow_pos_of_pos hT _)
    Summable (fun i => ‖gamma0BareCuspidalTerm N h r s Y hY m n hm hn i‖) ∧
      IntegrableOn (gamma0BareContinuousRhoIntegrand N h r s Y hY m n hm hn) (Ioi (0 : ℝ)) ∧
      Tendsto (fun k : ℕ => gamma0HeatSourceSpectralSide N h r s Y hY m n hm hn ((k : ℝ)+1))
        atTop (𝓝 (gamma0BareSourceSpectralSide N h r s Y hY m n hm hn)) := by
  dsimp only
  obtain ⟨hReal,hNorm⟩ := spectralABLRegularEnergyTest_axis_positive T (T^(1-ε)) hT (Real.rpow_pos_of_pos hT _)
  exact gamma0HeatSourceSpectralSide_tendsto_bare N _ r s Y hY m n hm hn
    (gamma0PrincipalCuspidalSymbol_norm_re_of_axis N _ hNorm) hReal hNorm
    (gamma0HeatRegular_source_diagonal_uniform N r Y hY m hm T ε hT)
    (gamma0HeatRegular_source_diagonal_uniform N s Y hY n hn T ε hT)

theorem gamma0HeatExceptional_source_tendsto_bare (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (a : ℝ) (A : ℕ) (hA : 3 ≤ A) :
    let h := spectralABLExceptionalEnergyTest a A (by omega)
    Summable (fun i => ‖gamma0BareCuspidalTerm N h r s Y hY m n hm hn i‖) ∧
      IntegrableOn (gamma0BareContinuousRhoIntegrand N h r s Y hY m n hm hn) (Ioi (0 : ℝ)) ∧
      Tendsto (fun k : ℕ => gamma0HeatSourceSpectralSide N h r s Y hY m n hm hn ((k : ℝ)+1))
        atTop (𝓝 (gamma0BareSourceSpectralSide N h r s Y hY m n hm hn)) := by
  dsimp only
  obtain ⟨hReal,hNorm⟩ := spectralABLExceptionalEnergyTest_axis_positive a A (by omega)
  exact gamma0HeatSourceSpectralSide_tendsto_bare N _ r s Y hY m n hm hn
    (gamma0PrincipalCuspidalSymbol_norm_re_of_axis N _ hNorm) hReal hNorm
    (gamma0HeatExceptional_source_diagonal_uniform N r Y hY m hm a A hA)
    (gamma0HeatExceptional_source_diagonal_uniform N s Y hY n hn a A hA)

end ArtinMatthews
