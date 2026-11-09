module

public import ArtinMatthews.SpectralBareEisensteinCoefficient
public import ArtinMatthews.SpectralGaussianMonotoneLimit
public import Mathlib.MeasureTheory.Integral.DominatedConvergence


set_option backward.privateInPublic true
@[expose] public section

/-! Gaussian extraction of the literal continuous source integral.
Measurability is recovered from the checked Gaussian test itself. -/

noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups Topology
namespace ArtinMatthews

theorem spectralHeatEnergyWeight_principal_cutoff (k : ℕ) (t : ℝ) :
    spectralHeatEnergyWeight ((k : ℝ)+1) (1/4+t^2) =
      (spectralGaussianCutoff k (2*t^2) : ℂ) := by
  rw [spectralHeatEnergyWeight_real,spectralGaussianCutoff]
  congr 2
  ring

theorem gamma0BareContinuousRhoIntegrand_aestronglyMeasurable (N : ℕ) [NeZero N]
    (h : SpectralEnergyTest) (r s : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y)
    (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) :
    AEStronglyMeasurable (gamma0BareContinuousRhoIntegrand N h r s Y hY m n hm hn)
      (volume.restrict (Ioi (0 : ℝ))) := by
  let W : ℝ → ℂ := fun t => spectralHeatEnergyWeight 1 (1/4+t^2)
  have hW : Measurable W := by unfold W spectralHeatEnergyWeight; fun_prop
  have hi := gamma0HeatContinuousRhoIntegrand_integrable N h r s Y hY m n hm hn 1 one_pos
  apply ((hi.aemeasurable.div hW.aemeasurable).aestronglyMeasurable).congr
  exact ae_of_all _ (fun t => by
    change gamma0HeatContinuousRhoIntegrand N h r s Y hY m n hm hn 1 t/W t =
      gamma0BareContinuousRhoIntegrand N h r s Y hY m n hm hn t
    rw [gamma0HeatContinuousRhoIntegrand_eq_bare]
    change _*W t/W t = _
    exact mul_div_cancel_right₀ _ (Complex.exp_ne_zero _))

theorem gamma0HeatContinuousRhoDiagonal_re (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0)
    (hReal : ∀ t : ℝ, ((spectralContinuousTestSymbol h t).re : ℂ) = spectralContinuousTestSymbol h t)
    (k : ℕ) (t : ℝ) :
    (gamma0HeatContinuousRhoIntegrand N h r r Y hY n n hn hn ((k : ℝ)+1) t).re =
      gamma0BareContinuousRhoDiagonal N h r Y hY n hn t*spectralGaussianCutoff k (2*t^2) := by
  rw [gamma0HeatContinuousRhoIntegrand_eq_bare,gamma0BareContinuousRhoIntegrand_diagonal
    N h r Y hY n hn t (hReal t),spectralHeatEnergyWeight_principal_cutoff,← Complex.ofReal_mul,Complex.ofReal_re]

theorem gamma0HeatContinuousRhoDiagonal_integral_re (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0)
    (hReal : ∀ t : ℝ, ((spectralContinuousTestSymbol h t).re : ℂ) = spectralContinuousTestSymbol h t)
    (k : ℕ) :
    (∫ t in Ioi (0 : ℝ), gamma0HeatContinuousRhoIntegrand N h r r Y hY n n hn hn ((k : ℝ)+1) t).re =
      ∫ t in Ioi (0 : ℝ), gamma0BareContinuousRhoDiagonal N h r Y hY n hn t*
        spectralGaussianCutoff k (2*t^2) := by
  have hi := gamma0HeatContinuousRhoIntegrand_integrable N h r r Y hY n n hn hn ((k : ℝ)+1) (by positivity)
  calc
    _ = ∫ t in Ioi (0 : ℝ), (gamma0HeatContinuousRhoIntegrand N h r r Y hY n n hn hn ((k : ℝ)+1) t).re :=
      (integral_re hi).symm
    _ = _ := integral_congr_ae (ae_of_all _ (gamma0HeatContinuousRhoDiagonal_re N h r Y hY n hn hReal k))

theorem gamma0BareContinuousRhoDiagonal_integrable (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0)
    (hReal : ∀ t : ℝ, ((spectralContinuousTestSymbol h t).re : ℂ) = spectralContinuousTestSymbol h t)
    (hPos : ∀ t : ℝ, 0 ≤ (spectralContinuousTestSymbol h t).re) (C : ℝ)
    (hC : ∀ k : ℕ, (∫ t in Ioi (0 : ℝ),
      gamma0HeatContinuousRhoIntegrand N h r r Y hY n n hn hn ((k : ℝ)+1) t).re ≤ C) :
    IntegrableOn (gamma0BareContinuousRhoDiagonal N h r Y hY n hn) (Ioi (0 : ℝ)) ∧
      (∫ t in Ioi (0 : ℝ), gamma0BareContinuousRhoDiagonal N h r Y hY n hn t) ≤ C := by
  let D := gamma0BareContinuousRhoDiagonal N h r Y hY n hn
  have hm := gamma0BareContinuousRhoIntegrand_aestronglyMeasurable N h r r Y hY n n hn hn
  have hD : AEStronglyMeasurable D (volume.restrict (Ioi (0 : ℝ))) := by
    apply (Complex.continuous_re.comp_aestronglyMeasurable hm).congr
    exact ae_of_all _ (fun t => by
      change (gamma0BareContinuousRhoIntegrand N h r r Y hY n n hn hn t).re = D t
      rw [gamma0BareContinuousRhoIntegrand_diagonal N h r Y hY n hn t (hReal t),Complex.ofReal_re])
  have hWeighted (k : ℕ) : IntegrableOn
      (fun t : ℝ => D t*spectralGaussianCutoff k (2*t^2)) (Ioi (0 : ℝ)) := by
    have hi := gamma0HeatContinuousRhoIntegrand_integrable N h r r Y hY n n hn hn ((k : ℝ)+1) (by positivity)
    exact hi.re.congr (ae_of_all _ (gamma0HeatContinuousRhoDiagonal_re N h r Y hY n hn hReal k))
  have hBound (k : ℕ) : (∫ t in Ioi (0 : ℝ), D t*spectralGaussianCutoff k (2*t^2)) ≤ C := by
    rw [← gamma0HeatContinuousRhoDiagonal_integral_re N h r Y hY n hn hReal k]
    exact hC k
  obtain ⟨hInt,hMass,_⟩ := integrable_of_uniform_gaussian_cutoffs (volume.restrict (Ioi (0 : ℝ))) D
    (fun t => 2*t^2) hD
    (ae_of_all _ (fun t => gamma0BareContinuousRhoDiagonal_nonneg N h r Y hY n hn t (hPos t)))
    (ae_of_all _ (fun t => by positivity)) hWeighted C hBound
  exact ⟨hInt,hMass⟩

theorem gamma0BareContinuousRhoIntegrand_integrable (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (r s : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (hPos : ∀ t : ℝ, ‖spectralContinuousTestSymbol h t‖ = (spectralContinuousTestSymbol h t).re)
    (hDr : IntegrableOn (gamma0BareContinuousRhoDiagonal N h r Y hY m hm) (Ioi (0 : ℝ)))
    (hDs : IntegrableOn (gamma0BareContinuousRhoDiagonal N h s Y hY n hn) (Ioi (0 : ℝ))) :
    IntegrableOn (gamma0BareContinuousRhoIntegrand N h r s Y hY m n hm hn) (Ioi (0 : ℝ)) := by
  have hmaj := (hDr.add hDs).div_const 2
  exact hmaj.mono'
    (gamma0BareContinuousRhoIntegrand_aestronglyMeasurable N h r s Y hY m n hm hn)
    (ae_of_all _ (fun t => gamma0BareContinuousRhoIntegrand_norm_le_diagonals N h r s Y hY m n hm hn t (hPos t)))

theorem gamma0HeatContinuousRhoIntegral_tendsto_bare (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (r s : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (hI : IntegrableOn (gamma0BareContinuousRhoIntegrand N h r s Y hY m n hm hn) (Ioi (0 : ℝ))) :
    Tendsto (fun R : ℝ => ∫ t in Ioi (0 : ℝ),
      gamma0HeatContinuousRhoIntegrand N h r s Y hY m n hm hn R t) atTop
      (𝓝 (∫ t in Ioi (0 : ℝ), gamma0BareContinuousRhoIntegrand N h r s Y hY m n hm hn t)) := by
  simp_rw [gamma0HeatContinuousRhoIntegrand_eq_bare]
  apply tendsto_integral_filter_of_dominated_convergence
    (fun t : ℝ => ‖gamma0BareContinuousRhoIntegrand N h r s Y hY m n hm hn t‖)
  · exact Eventually.of_forall (fun R => hI.aestronglyMeasurable.mul
      (show Measurable (fun t : ℝ => spectralHeatEnergyWeight R (1/4+t^2)) from by
        unfold spectralHeatEnergyWeight
        fun_prop).aestronglyMeasurable)
  · exact Eventually.of_forall (fun R => Eventually.of_forall (fun t => by
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _)
        (spectralHeatEnergyWeight_principal_norm_le R (1/4+t^2) (by nlinarith [sq_nonneg t]))))
  · exact hI.norm
  · exact Eventually.of_forall (fun t => by
      simpa only [mul_one] using tendsto_const_nhds.mul (spectralHeatEnergyWeight_tendsto (1/4+t^2)))

end ArtinMatthews
