module

public import ArtinMatthews.SpectralABLOppositeForwardTrace


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set MeasureTheory Complex OAI.CubicEisenstein
open scoped MatrixGroups ContDiff ComplexConjugate
noncomputable section

theorem spectralABLOppositeFourierWeight_add_mul (f g : ℝ → ℂ) (c : ℂ)
    (hf : Continuous f) (hfc : HasCompactSupport f) (hfp : tsupport f ⊆ Ioi (0 : ℝ))
    (hg : Continuous g) (hgc : HasCompactSupport g) (hgp : tsupport g ⊆ Ioi (0 : ℝ))
    (z : ℂ) :
    spectralABLOppositeFourierWeight (fun x => f x+c*g x) z =
      spectralABLOppositeFourierWeight f z+c*spectralABLOppositeFourierWeight g z := by
  let ν := 2*I*z
  have hfI := spectralKLCompactOrderIntegrand_integrable f hf hfc hfp ν
  have hgI := spectralKLCompactOrderIntegrand_integrable g hg hgc hgp ν
  have he : spectralKLCompactOrderIntegrand (fun x => f x+c*g x) ν =
      fun x => spectralKLCompactOrderIntegrand f ν x+c*spectralKLCompactOrderIntegrand g ν x := by
    funext x
    simp only [spectralKLCompactOrderIntegrand,spectralKLPhysicalCompactDiv]
    ring
  change (2/(Real.pi : ℂ))*spectralKLCompactOrderTransform (fun x => f x+c*g x) ν =
    (2/(Real.pi : ℂ))*spectralKLCompactOrderTransform f ν+
      c*((2/(Real.pi : ℂ))*spectralKLCompactOrderTransform g ν)
  unfold spectralKLCompactOrderTransform
  rw [he,integral_add hfI (hgI.const_mul c),integral_const_mul]
  ring

theorem gamma0BareSourceSpectralSide_add_mul (N : ℕ) [NeZero N] (h h₁ h₂ : SpectralEnergyTest)
    (c : ℂ) (hh : ∀ l, h l = h₁ l+c*h₂ l)
    (r s : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (hS₁ : Summable (fun i => ‖gamma0BareCuspidalTerm N h₁ r s Y hY m n hm hn i‖))
    (hS₂ : Summable (fun i => ‖gamma0BareCuspidalTerm N h₂ r s Y hY m n hm hn i‖))
    (hI₁ : IntegrableOn (gamma0BareContinuousRhoIntegrand N h₁ r s Y hY m n hm hn) (Ioi (0 : ℝ)))
    (hI₂ : IntegrableOn (gamma0BareContinuousRhoIntegrand N h₂ r s Y hY m n hm hn) (Ioi (0 : ℝ))) :
    gamma0BareSourceSpectralSide N h r s Y hY m n hm hn =
      gamma0BareSourceSpectralSide N h₁ r s Y hY m n hm hn+
        c*gamma0BareSourceSpectralSide N h₂ r s Y hY m n hm hn := by
  let F (q : SpectralEnergyTest) := gamma0BareCuspidalTerm N q r s Y hY m n hm hn
  let E (q : SpectralEnergyTest) := gamma0BareContinuousRhoIntegrand N q r s Y hY m n hm hn
  let R (q : SpectralEnergyTest) := gamma0BareResidualRhoTerm N q r s m n hm hn
  have hF : F h = fun i => F h₁ i+c*F h₂ i := by
    funext i
    simp only [F,gamma0BareCuspidalTerm,gamma0CuspidalTestSymbol,hh]
    ring
  have hE : E h = fun t => E h₁ t+c*E h₂ t := by
    funext t
    simp only [E,gamma0BareContinuousRhoIntegrand,spectralContinuousTestSymbol_apply,hh]
    ring
  have hR (l : Ici (0 : ℝ)) (j : Fin (Module.finrank ℂ (gamma0ResidualEnergyEigenspace N l))) :
      R h l j = R h₁ l j+c*R h₂ l j := by
    simp only [R,gamma0BareResidualRhoTerm,hh]
    ring
  have hsum : (∑' i, F h i) = (∑' i, F h₁ i)+c*(∑' i, F h₂ i) := by
    rw [hF,hS₁.of_norm.tsum_add (hS₂.of_norm.mul_left c),tsum_mul_left]
  have hint : (∫ t in Ioi (0 : ℝ), E h t) =
      (∫ t in Ioi (0 : ℝ), E h₁ t)+c*(∫ t in Ioi (0 : ℝ), E h₂ t) := by
    rw [hE,integral_add hI₁ (hI₂.const_mul c),integral_const_mul]
  have hres : gamma0BareResidualRhoSum N h r s m n hm hn =
      gamma0BareResidualRhoSum N h₁ r s m n hm hn+c*gamma0BareResidualRhoSum N h₂ r s m n hm hn := by
    change (∑ l∈gamma0ResidualEnergyWindow N, ∑ j, R h l j) =
      (∑ l∈gamma0ResidualEnergyWindow N, ∑ j, R h₁ l j)+
        c*(∑ l∈gamma0ResidualEnergyWindow N, ∑ j, R h₂ l j)
    simp_rw [hR,Finset.sum_add_distrib,← Finset.mul_sum]
  change (∑' i, F h i)+((∫ t in Ioi (0 : ℝ), E h t)+gamma0BareResidualRhoSum N h r s m n hm hn) =
    ((∑' i, F h₁ i)+((∫ t in Ioi (0 : ℝ), E h₁ t)+gamma0BareResidualRhoSum N h₁ r s m n hm hn))+
      c*((∑' i, F h₂ i)+((∫ t in Ioi (0 : ℝ), E h₂ t)+gamma0BareResidualRhoSum N h₂ r s m n hm hn))
  rw [hsum,hint,hres]
  ring

/-- The opposite-sign source trace for an arbitrary complex smooth
compact test. Each spectral sector has its original normalization. -/
theorem gamma0ABLOpposite_forward_trace (N : ℕ) [NeZero N] (r s : SL(2, ℤ))
    (hchart : r = s ∨ ¬ gamma0EisensteinCuspsEquivalent N r s)
    (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) (hmn : m*n < 0)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hp : tsupport f ⊆ Ioi (0 : ℝ)) :
    let h := spectralABLOppositeEnergyTest f hf hc hp
    Summable (fun c : Ioi (0 : ℕ) => gamma0ABLOppositeGeometricTerm N r s c m n f) ∧
    Summable (fun i => ‖gamma0BareCuspidalTerm N h r s Y hY m n hm hn i‖) ∧
    IntegrableOn (gamma0BareContinuousRhoIntegrand N h r s Y hY m n hm hn) (Ioi (0 : ℝ)) ∧
    gamma0BareSourceSpectralSide N h r s Y hY m n hm hn =
      (1/(4*(Real.pi : ℂ)))*(∑' c : Ioi (0 : ℕ), gamma0ABLOppositeGeometricTerm N r s c m n f) := by
  let f₁ : ℝ → ℂ := fun x => ((f x).re : ℂ)
  let f₂ : ℝ → ℂ := fun x => ((f x).im : ℂ)
  have h₁ : ContDiff ℝ ∞ f₁ := Complex.ofRealCLM.contDiff.comp (Complex.reCLM.contDiff.comp hf)
  have h₂ : ContDiff ℝ ∞ f₂ := Complex.ofRealCLM.contDiff.comp (Complex.imCLM.contDiff.comp hf)
  have hs₁ : tsupport f₁ ⊆ tsupport f := by
    apply closure_mono
    intro x hx
    exact fun hfx => hx (by simp [f₁,hfx])
  have hs₂ : tsupport f₂ ⊆ tsupport f := by
    apply closure_mono
    intro x hx
    exact fun hfx => hx (by simp [f₂,hfx])
  have hc₁ : HasCompactSupport f₁ := hc.of_isClosed_subset (isClosed_tsupport _) hs₁
  have hc₂ : HasCompactSupport f₂ := hc.of_isClosed_subset (isClosed_tsupport _) hs₂
  have hp₁ := hs₁.trans hp
  have hp₂ := hs₂.trans hp
  have hr₁ (x : ℝ) : star (f₁ x) = f₁ x := by simp [f₁,Complex.star_def]
  have hr₂ (x : ℝ) : star (f₂ x) = f₂ x := by simp [f₂,Complex.star_def]
  have hdecomp : f = fun x => f₁ x+I*f₂ x := by
    funext x
    apply Complex.ext <;> simp [f₁,f₂,Complex.mul_re,Complex.mul_im]
  let h := spectralABLOppositeEnergyTest f hf hc hp
  let q₁ := spectralABLOppositeEnergyTest f₁ h₁ hc₁ hp₁
  let q₂ := spectralABLOppositeEnergyTest f₂ h₂ hc₂ hp₂
  have hh (l : Ici (0 : ℝ)) : h l = q₁ l+I*q₂ l := by
    change spectralABLOppositeFourierWeight f (spectralSourceParameter l) =
      spectralABLOppositeFourierWeight f₁ (spectralSourceParameter l)+
        I*spectralABLOppositeFourierWeight f₂ (spectralSourceParameter l)
    have he := spectralABLOppositeFourierWeight_add_mul f₁ f₂ I h₁.continuous hc₁ hp₁
      h₂.continuous hc₂ hp₂ (spectralSourceParameter l)
    rwa [← hdecomp] at he
  obtain ⟨hg₁,hS₁,hI₁,he₁⟩ := gamma0ABLOpposite_forward_trace_real N r s hchart Y hY m n hm hn hmn
    f₁ h₁ hc₁ hp₁ hr₁
  obtain ⟨hg₂,hS₂,hI₂,he₂⟩ := gamma0ABLOpposite_forward_trace_real N r s hchart Y hY m n hm hn hmn
    f₂ h₂ hc₂ hp₂ hr₂
  obtain ⟨hS,hI⟩ := gamma0OppositeBareSpectrum_integrable N r s Y hY m n hm hn f hf hc hp
  let G (p : ℝ → ℂ) (k : Ioi (0 : ℕ)) := gamma0ABLOppositeGeometricTerm N r s k m n p
  have hG : G f = fun k => G f₁ k+I*G f₂ k := by
    funext k
    dsimp only [G,gamma0ABLOppositeGeometricTerm]
    rw [congrFun hdecomp]
    ring
  have hsum : (∑' k, G f k) = (∑' k, G f₁ k)+I*(∑' k, G f₂ k) := by
    rw [hG,hg₁.tsum_add (hg₂.mul_left I),tsum_mul_left]
  refine ⟨?_,hS,hI,?_⟩
  · change Summable (G f)
    rw [hG]
    exact hg₁.add (hg₂.mul_left I)
  · change gamma0BareSourceSpectralSide N h r s Y hY m n hm hn =
      (1/(4*(Real.pi : ℂ)))*(∑' k, G f k)
    rw [gamma0BareSourceSpectralSide_add_mul N h q₁ q₂ I hh r s Y hY m n hm hn hS₁ hS₂ hI₁ hI₂,
      he₁,he₂,hsum]
    ring

end
end ArtinMatthews
