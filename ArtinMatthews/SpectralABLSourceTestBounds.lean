module

public import ArtinMatthews.SpectralJNativeSymbols
public import ArtinMatthews.SpectralJForwardRealWeight
public import ArtinMatthews.SpectralABLOppositeKWeight
public import ArtinMatthews.SpectralPrincipalDecayWeight
public import ArtinMatthews.SpectralABLResidualExceptionalMoment


set_option backward.privateInPublic true
@[expose] public section

/-! Literal energy symbols for the two forward transforms, including
the cosine denominator on the proved nonzero-mode support. -/

noncomputable section
open Set
open scoped ContDiff
namespace ArtinMatthews

def spectralABLPrincipalSymbolBound (h : SpectralEnergyTest) (H Z : ℝ) : Prop :=
  ∀ t : ℝ, ‖spectralContinuousTestSymbol h t‖ ≤
    H*spectralPrincipalDecayWeight Z t/Real.cosh (Real.pi*t)

def spectralABLComplementarySymbolBound (h : SpectralEnergyTest) (H a : ℝ) : Prop :=
  ∀ l : Ici (0 : ℝ), 3/16 ≤ (l : ℝ) → (l : ℝ) ≤ 1/4 →
    ‖h l‖ ≤ H*a^(-2*Real.sqrt (1/4-(l : ℝ)))/
      Real.cos (Real.pi*Real.sqrt (1/4-(l : ℝ)))

theorem spectralSourceParameter_complementary_eq (l : ℝ) (hl : l ≤ 1/4) :
    spectralSourceParameter l = (Real.sqrt (1/4-l) : ℂ)*Complex.I := by
  unfold spectralSourceParameter
  rw [Real.sqrt_eq_zero_of_nonpos (sub_nonpos.mpr hl),Complex.ofReal_zero,zero_add]

theorem spectralSourceParameter_cosh_norm_complementary (l : ℝ)
    (hl : 3/16 ≤ l) (hl₁ : l ≤ 1/4) :
    ‖Complex.cosh ((Real.pi : ℂ)*spectralSourceParameter l)‖ =
      Real.cos (Real.pi*Real.sqrt (1/4-l)) := by
  have hPos : 0 < Real.cos (Real.pi*Real.sqrt (1/4-l)) :=
    (show 0 < Real.cos (Real.pi/4) by rw [Real.cos_pi_div_four]; positivity).trans_le
      (spectral_cosine_complementary_lower_of_gap hl)
  rw [spectralSourceParameter_complementary_eq l hl₁,← mul_assoc,← Complex.ofReal_mul,
    Complex.cosh_mul_I,← Complex.ofReal_cos,Complex.norm_real,Real.norm_of_nonneg hPos.le]

theorem spectralJClippedEnergyTest_symbol_bounds
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ))
    {H Z a : ℝ}
    (hP : ∀ t : ℝ, ‖spectralJForwardTransform f (t : ℂ)‖ ≤ H*spectralPrincipalDecayWeight Z t)
    (hE : ∀ κ : ℝ, 0 ≤ κ → κ ≤ 1/4 →
      ‖spectralJForwardTransform f ((κ : ℂ)*Complex.I)‖ ≤ H*a^(-2*κ)) :
    spectralABLPrincipalSymbolBound (spectralJClippedEnergyTest f hf hc hp) (Real.pi*H) Z ∧
      spectralABLComplementarySymbolBound (spectralJClippedEnergyTest f hf hc hp) (Real.pi*H) a := by
  constructor
  · intro t
    rw [spectralJClippedEnergyTest_continuous_symbol,spectralJForwardSpectralWeight_norm_real]
    calc
      _ ≤ (Real.pi/Real.cosh (Real.pi*t))*(H*spectralPrincipalDecayWeight Z t) :=
        mul_le_mul_of_nonneg_left (hP t) (by positivity)
      _ = _ := by ring
  · intro l hl hl₁
    let κ := Real.sqrt (1/4-(l : ℝ))
    have hκ : 0 ≤ κ := Real.sqrt_nonneg _
    have hκ₁ : κ ≤ 1/4 := Real.sqrt_le_iff.mpr ⟨by norm_num,by linarith⟩
    have hCos := spectralSourceParameter_cosh_norm_complementary (l : ℝ) hl hl₁
    have hParam : spectralSourceParameter (l : ℝ) = (κ : ℂ)*Complex.I :=
      spectralSourceParameter_complementary_eq _ hl₁
    change ‖spectralJClippedWeight f (l : ℝ)‖ ≤ _
    rw [spectralJClippedWeight_native f _ hl,spectralJForwardSpectralWeight,norm_mul,norm_div,
      Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le,hCos,hParam]
    have hnonneg : 0 ≤ Real.cos (Real.pi*κ) :=
      ((show 0 < Real.cos (Real.pi/4) by rw [Real.cos_pi_div_four]; positivity).trans_le
        (spectral_cosine_complementary_lower_of_gap hl)).le
    calc
      _ = (Real.pi*‖spectralJForwardTransform f ((κ : ℂ)*Complex.I)‖)/Real.cos (Real.pi*κ) := by ring
      _ ≤ (Real.pi*(H*a^(-2*κ)))/Real.cos (Real.pi*κ) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hE κ hκ hκ₁) Real.pi_pos.le) hnonneg
      _ = _ := by ring

theorem spectralABLOppositeEnergyTest_symbol_bounds
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ))
    {H Z a : ℝ}
    (hP : ∀ t : ℝ, ‖spectralABLOppositeTransform f (t : ℂ)‖ ≤ H*spectralPrincipalDecayWeight Z t)
    (hE : ∀ κ : ℝ, 0 ≤ κ → κ ≤ 1/4 →
      ‖spectralABLOppositeTransform f ((κ : ℂ)*Complex.I)‖ ≤ H*a^(-2*κ)) :
    spectralABLPrincipalSymbolBound (spectralABLOppositeEnergyTest f hf hc hp) H Z ∧
      spectralABLComplementarySymbolBound (spectralABLOppositeEnergyTest f hf hc hp) H a := by
  constructor
  · intro t
    have hp₀ := hP t
    rw [spectralABLOppositeTransform,norm_mul,← Complex.ofReal_mul,← Complex.ofReal_cosh,
      Complex.norm_real,Real.norm_of_nonneg (Real.cosh_pos _).le] at hp₀
    rw [spectralABLOppositeEnergyTest_continuous_symbol]
    exact (le_div_iff₀ (Real.cosh_pos _)).mpr (by rw [mul_comm]; exact hp₀)
  · intro l hl hl₁
    let κ := Real.sqrt (1/4-(l : ℝ))
    have hκ : 0 ≤ κ := Real.sqrt_nonneg _
    have hκ₁ : κ ≤ 1/4 := Real.sqrt_le_iff.mpr ⟨by norm_num,by linarith⟩
    have hCos := spectralSourceParameter_cosh_norm_complementary (l : ℝ) hl hl₁
    have hParam : spectralSourceParameter (l : ℝ) = (κ : ℂ)*Complex.I :=
      spectralSourceParameter_complementary_eq _ hl₁
    have hp₀ := hE κ hκ hκ₁
    rw [← hParam,spectralABLOppositeTransform,norm_mul,hCos] at hp₀
    rw [spectralABLOppositeEnergyTest_apply]
    apply (le_div_iff₀ ?_).mpr
    · rw [mul_comm]
      exact hp₀
    · exact (show 0 < Real.cos (Real.pi/4) by rw [Real.cos_pi_div_four]; positivity).trans_le
        (spectral_cosine_complementary_lower_of_gap hl)

end ArtinMatthews
