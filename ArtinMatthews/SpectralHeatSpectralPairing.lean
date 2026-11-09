module

public import ArtinMatthews.SpectralNativeHeatCoefficients
public import ArtinMatthews.SpectralHeatEnergyWeight
public import ArtinMatthews.SpectralABLRhoPairing


set_option backward.privateInPublic true
@[expose] public section

/-! The full source-normalized spectral expansion of two actual
Gaussian native tests. All continuous and residual terms are retained. -/

noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups ContDiff InnerProductSpace
namespace ArtinMatthews

theorem gamma0HeatPoincareTest_cusp_term (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (i : Gamma0AllHeightSpectralIndex N) (r s : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y)
    (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) (R : ℝ) (hR : 0 < R) :
    gamma0CuspidalTestSymbol N ((1/4 : ℂ) • h) i*
      (inner ℂ (gamma0HeatPoincareTest N r m hm R hR) (gamma0FullCuspidalSpectralBasis N i).val*
        inner ℂ (gamma0FullCuspidalSpectralBasis N i).val (gamma0HeatPoincareTest N s n hn R hR)) =
      gamma0CuspidalTestSymbol N h i*
        (((Real.sqrt |(m : ℝ)| : ℂ)*gamma0ABLSourceRho N i r Y hY m hm)*
          star ((Real.sqrt |(n : ℝ)| : ℂ)*gamma0ABLSourceRho N i s Y hY n hn))*
        spectralHeatEnergyWeight R (gamma0AllHeightGradientSpectralValue N i) := by
  have hc : inner ℂ (gamma0FullCuspidalSpectralBasis N i).val (gamma0HeatPoincareTest N s n hn R hR) =
      star (inner ℂ (gamma0HeatPoincareTest N s n hn R hR) (gamma0FullCuspidalSpectralBasis N i).val) :=
    (inner_conj_symm (𝕜 := ℂ) (gamma0FullCuspidalSpectralBasis N i).val
      (gamma0HeatPoincareTest N s n hn R hR)).symm
  rw [hc,gamma0HeatPoincareTest_cuspidal_coefficient N i r Y hY m hm R hR,
    gamma0HeatPoincareTest_cuspidal_coefficient N i s Y hY n hn R hR]
  change ((1/4 : ℂ)*gamma0CuspidalTestSymbol N h i)*_ = _
  rw [← spectralHeatEnergyWeight_product]
  simp only [star_mul]
  norm_num
  ring

theorem gamma0HeatPoincareTest_continuous_pair_ae (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (R : ℝ) (hR : 0 < R) :
    gamma0EisensteinChannelPair N
      (gamma0EisensteinAnalysis N (gamma0HeatPoincareTest N r m hm R hR))
      (gamma0EisensteinAnalysis N (gamma0HeatPoincareTest N s n hn R hR))
      =ᵐ[gamma0EisensteinSpectralMeasure] fun t =>
        gamma0PrimitiveContinuousFourierKernel N r s Y hY m n hm hn t*
          spectralHeatEnergyWeight R (1/4+t^2) := by
  have hr := ae_all_iff.mpr (fun i => gamma0HeatPoincareTest_continuous_ae N r m hm R hR Y hY i)
  have hs := ae_all_iff.mpr (fun i => gamma0HeatPoincareTest_continuous_ae N s n hn R hR Y hY i)
  filter_upwards [hr,hs] with t hrt hst
  unfold gamma0EisensteinChannelPair gamma0PrimitiveContinuousFourierKernel
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [hrt i,hst i,RCLike.inner_apply]
  have hdouble (z : ℂ) : (starRingEnd ℂ) (star z) = z := star_star z
  rw [hdouble]
  have he : Complex.exp (-((t : ℂ)^2)/(R : ℂ)^2)*
      star (Complex.exp (-((t : ℂ)^2)/(R : ℂ)^2)) = spectralHeatEnergyWeight R (1/4+t^2) := by
    have hs : star (Complex.exp (-((t : ℂ)^2)/(R : ℂ)^2)) =
        Complex.exp (-((t : ℂ)^2)/(R : ℂ)^2) := by
      have hr : -((t : ℂ)^2)/(R : ℂ)^2 = ((-(t^2)/R^2 : ℝ) : ℂ) := by
        push_cast
        rfl
      rw [hr,← Complex.ofReal_exp]
      exact Complex.conj_ofReal _
    rw [hs,← Complex.exp_add,spectralHeatEnergyWeight]
    congr 1
    push_cast
    ring
  rw [← he]
  simp only [star_mul]
  ring

def gamma0HeatContinuousRhoIntegrand (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (r s : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (R t : ℝ) : ℂ :=
  spectralContinuousTestSymbol h t*
    ((Real.sqrt |(m : ℝ)| : ℂ)*(Real.sqrt |(n : ℝ)| : ℂ)*
      gamma0ABLContinuousRhoKernel N r s Y hY m n hm hn t)*
    spectralHeatEnergyWeight R (1/4+t^2)/((2*Real.pi : ℝ) : ℂ)

theorem gamma0HeatPoincareTest_continuous_integral (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (r s : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (R : ℝ) (hR : 0 < R) :
    (∫ t, spectralContinuousTestSymbol ((1/4 : ℂ) • h) t*
      gamma0EisensteinChannelPair N
        (gamma0EisensteinAnalysis N (gamma0HeatPoincareTest N r m hm R hR))
        (gamma0EisensteinAnalysis N (gamma0HeatPoincareTest N s n hn R hR)) t
      ∂gamma0EisensteinSpectralMeasure) =
    ∫ t in Ioi 0, gamma0HeatContinuousRhoIntegrand N h r s Y hY m n hm hn R t := by
  calc
    _ = ∫ t, spectralContinuousTestSymbol ((1/4 : ℂ) • h) t*
        (gamma0PrimitiveContinuousFourierKernel N r s Y hY m n hm hn t*
          spectralHeatEnergyWeight R (1/4+t^2)) ∂gamma0EisensteinSpectralMeasure := by
      apply integral_congr_ae
      filter_upwards [gamma0HeatPoincareTest_continuous_pair_ae N r s Y hY m n hm hn R hR] with t ht
      rw [ht]
    _ = _ := by
      have hp : 0 ≤ (2*Real.pi)⁻¹ := by positivity
      rw [gamma0EisensteinSpectralMeasure,integral_smul_measure,ENNReal.toReal_ofReal hp,
        Complex.real_smul,← integral_const_mul]
      apply integral_congr_ae
      exact ae_of_all _ (fun t => by
        dsimp only
        rw [gamma0PrimitiveContinuousFourierKernel_sourceRho]
        change (((2*Real.pi)⁻¹ : ℝ) : ℂ)*(((1/4 : ℂ)*spectralContinuousTestSymbol h t)*_)=_
        unfold gamma0HeatContinuousRhoIntegrand
        rw [Complex.ofReal_inv]
        ring)


theorem gamma0HeatContinuousRhoIntegrand_integrable (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (r s : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (R : ℝ) (hR : 0 < R) :
    IntegrableOn (gamma0HeatContinuousRhoIntegrand N h r s Y hY m n hm hn R) (Ioi 0) := by
  let f := fun t : ℝ => spectralContinuousTestSymbol h t*
    ((Real.sqrt |(m : ℝ)| : ℂ)*(Real.sqrt |(n : ℝ)| : ℂ)*
      gamma0ABLContinuousRhoKernel N r s Y hY m n hm hn t)*spectralHeatEnergyWeight R (1/4+t^2)
  have hi := gamma0EisensteinTestMultiplier_pair_integrable N ((1/4 : ℂ) • h)
    (gamma0EisensteinAnalysis N (gamma0HeatPoincareTest N r m hm R hR))
    (gamma0EisensteinAnalysis N (gamma0HeatPoincareTest N s n hn R hR))
  have hf : Integrable f gamma0EisensteinSpectralMeasure := by
    apply hi.congr
    filter_upwards [gamma0HeatPoincareTest_continuous_pair_ae N r s Y hY m n hm hn R hR] with t ht
    rw [ht,gamma0PrimitiveContinuousFourierKernel_sourceRho]
    change ((1/4 : ℂ)*spectralContinuousTestSymbol h t)*_ = _
    dsimp only [f]
    ring
  have hf0 : IntegrableOn f (Ioi (0 : ℝ)) := by
    unfold gamma0EisensteinSpectralMeasure at hf
    exact (integrable_smul_measure (by positivity) ENNReal.ofReal_ne_top).mp hf
  exact hf0.div_const _


def gamma0ResidualABLSourceRho (N : ℕ) [NeZero N] (l : Ici (0 : ℝ))
    (j : Fin (Module.finrank ℂ (gamma0ResidualEnergyEigenspace N l)))
    (r : SL(2, ℤ)) (n : ℤ) (hn : n ≠ 0) : ℂ :=
  gamma0AmbientABLSourceRho N l l.property (gamma0ResidualEigenbasis N l j).val
    (gamma0ResidualEigenbasis_green N l j) r n hn

theorem gamma0HeatPoincareTest_residual_term (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (l : Ici (0 : ℝ)) (j : Fin (Module.finrank ℂ (gamma0ResidualEnergyEigenspace N l)))
    (r s : SL(2, ℤ)) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) (R : ℝ) (hR : 0 < R) :
    ((1/4 : ℂ) • h) l*
      (inner ℂ (gamma0HeatPoincareTest N r m hm R hR) (gamma0ResidualEigenbasis N l j).val*
        inner ℂ (gamma0ResidualEigenbasis N l j).val (gamma0HeatPoincareTest N s n hn R hR)) =
      h l*(((Real.sqrt |(m : ℝ)| : ℂ)*gamma0ResidualABLSourceRho N l j r m hm)*
        star ((Real.sqrt |(n : ℝ)| : ℂ)*gamma0ResidualABLSourceRho N l j s n hn))*
        spectralHeatEnergyWeight R l := by
  have hc : inner ℂ (gamma0ResidualEigenbasis N l j).val (gamma0HeatPoincareTest N s n hn R hR) =
      star (inner ℂ (gamma0HeatPoincareTest N s n hn R hR) (gamma0ResidualEigenbasis N l j).val) :=
    (inner_conj_symm (𝕜 := ℂ) (gamma0ResidualEigenbasis N l j).val
      (gamma0HeatPoincareTest N s n hn R hR)).symm
  rw [hc,gamma0HeatPoincareTest_ambient_source_coefficient N l l.property _ (gamma0ResidualEigenbasis_green N l j)
      r m hm R hR,
    gamma0HeatPoincareTest_ambient_source_coefficient N l l.property _ (gamma0ResidualEigenbasis_green N l j)
      s n hn R hR]
  change ((1/4 : ℂ)*h l)*_ = _
  unfold gamma0ResidualABLSourceRho
  rw [← spectralHeatEnergyWeight_product]
  simp only [star_mul]
  norm_num
  ring

theorem gamma0HeatPoincareTest_source_pairing (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (r s : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (R : ℝ) (hR : 0 < R) :
    let u := gamma0HeatPoincareTest N r m hm R hR
    let v := gamma0HeatPoincareTest N s n hn R hR
    inner ℂ u (gamma0AmbientTestOperator N ((1/4 : ℂ) • h) v) =
      (∑' i : Gamma0AllHeightSpectralIndex N,
        gamma0CuspidalTestSymbol N h i*
          (((Real.sqrt |(m : ℝ)| : ℂ)*gamma0ABLSourceRho N i r Y hY m hm)*
            star ((Real.sqrt |(n : ℝ)| : ℂ)*gamma0ABLSourceRho N i s Y hY n hn))*
          spectralHeatEnergyWeight R (gamma0AllHeightGradientSpectralValue N i))+
      ((∫ t in Ioi 0, gamma0HeatContinuousRhoIntegrand N h r s Y hY m n hm hn R t)+
        ∑ l∈gamma0ResidualEnergyWindow N,
          ∑ j,h l*(((Real.sqrt |(m : ℝ)| : ℂ)*gamma0ResidualABLSourceRho N l j r m hm)*
            star ((Real.sqrt |(n : ℝ)| : ℂ)*gamma0ResidualABLSourceRho N l j s n hn))*
              spectralHeatEnergyWeight R l) := by
  dsimp only
  rw [gamma0AmbientTestOperator_pair,gamma0HeatPoincareTest_continuous_integral N h r s Y hY m n hm hn R hR]
  congr 1
  · apply tsum_congr
    intro i
    exact gamma0HeatPoincareTest_cusp_term N h i r s Y hY m n hm hn R hR
  · congr 1
    apply Finset.sum_congr rfl
    intro l _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact gamma0HeatPoincareTest_residual_term N h l j r s m n hm hn R hR


def gamma0HeatSourceSpectralSide (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (r s : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) (R : ℝ) : ℂ :=
  (∑' i : Gamma0AllHeightSpectralIndex N,
    gamma0CuspidalTestSymbol N h i*
      (((Real.sqrt |(m : ℝ)| : ℂ)*gamma0ABLSourceRho N i r Y hY m hm)*
        star ((Real.sqrt |(n : ℝ)| : ℂ)*gamma0ABLSourceRho N i s Y hY n hn))*
      spectralHeatEnergyWeight R (gamma0AllHeightGradientSpectralValue N i))+
  ((∫ t in Ioi 0, gamma0HeatContinuousRhoIntegrand N h r s Y hY m n hm hn R t)+
    ∑ l∈gamma0ResidualEnergyWindow N,
      ∑ j,h l*(((Real.sqrt |(m : ℝ)| : ℂ)*gamma0ResidualABLSourceRho N l j r m hm)*
        star ((Real.sqrt |(n : ℝ)| : ℂ)*gamma0ResidualABLSourceRho N l j s n hn))*
          spectralHeatEnergyWeight R l)

theorem gamma0HeatPoincareTest_source_pairing_eq (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (r s : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (R : ℝ) (hR : 0 < R) :
    inner ℂ (gamma0HeatPoincareTest N r m hm R hR)
      (gamma0AmbientTestOperator N ((1/4 : ℂ) • h) (gamma0HeatPoincareTest N s n hn R hR)) =
    gamma0HeatSourceSpectralSide N h r s Y hY m n hm hn R :=
  gamma0HeatPoincareTest_source_pairing N h r s Y hY m n hm hn R hR

theorem gamma0HeatPoincareTest_source_cusp_summable (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (r s : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (R : ℝ) (hR : 0 < R) :
    Summable (fun i : Gamma0AllHeightSpectralIndex N =>
      gamma0CuspidalTestSymbol N h i*
        (((Real.sqrt |(m : ℝ)| : ℂ)*gamma0ABLSourceRho N i r Y hY m hm)*
          star ((Real.sqrt |(n : ℝ)| : ℂ)*gamma0ABLSourceRho N i s Y hY n hn))*
        spectralHeatEnergyWeight R (gamma0AllHeightGradientSpectralValue N i)) := by
  have hs := gamma0CuspidalTestOperator_pair_summable N ((1/4 : ℂ) • h)
    (gamma0HeatPoincareTest N r m hm R hR) (gamma0HeatPoincareTest N s n hn R hR)
  exact hs.congr (fun i => gamma0HeatPoincareTest_cusp_term N h i r s Y hY m n hm hn R hR)

end ArtinMatthews
