module

public import ArtinMatthews.SpectralNativeWindowAction
public import ArtinMatthews.SpectralNativeCompactProfile
public import ArtinMatthews.SpectralAmbientMultiplierLinearity
public import ArtinMatthews.SpectralABLCorrectedInverse
public import ArtinMatthews.SpectralKLWindowDerivatives
public import ArtinMatthews.SpectralABLRhoPairing


set_option backward.privateInPublic true
@[expose] public section

/-! The literal ABL windows act on genuine primitive Poincare tests.
The full ambient action and its source-normalized quarter are both retained. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups ContDiff
namespace ArtinMatthews

def gamma0PrimitivePhysicalTest (N : ℕ) [NeZero N] (r : SL(2, ℤ))
    (n : ℤ) (ρ : ℝ → ℝ) : ℝ → ℂ :=
  spectralKLHeightPhysicalTest |cuspFourierFrequency 1 n|
    (fun y => ρ ((gamma0CuspTrueWidth N r : ℝ)*y))

theorem gamma0PrimitivePhysicalTest_eq (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (n : ℤ) (hn : n ≠ 0) (ρ : ℝ → ℝ) (F : ℝ → ℂ)
    (hzero : ∀ x : ℝ, x ≤ 0 → F x = 0)
    (hpositive : ∀ x : ℝ, 0 < x → gamma0PrimitivePhysicalTest N r n ρ x = F x) :
    gamma0PrimitivePhysicalTest N r n ρ = F := by
  funext x
  by_cases hx : 0 < x
  · exact hpositive x hx
  · rw [hzero x (le_of_not_gt hx)]
    exact spectralKLHeightPhysicalTest_nonpos
      (abs_pos.mpr (cuspFourierFrequency_ne_zero 1 zero_lt_one n hn)) _ (le_of_not_gt hx)

theorem gamma0PrimitivePhysicalTest_properties (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (n : ℤ) (hn : n ≠ 0) (ρ : ℝ → ℝ)
    (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) :
    ContDiff ℝ ∞ (gamma0PrimitivePhysicalTest N r n ρ) ∧
    HasCompactSupport (gamma0PrimitivePhysicalTest N r n ρ) ∧
    tsupport (gamma0PrimitivePhysicalTest N r n ρ) ⊆ Ioi (0 : ℝ) ∧
    (∀ x, star (gamma0PrimitivePhysicalTest N r n ρ x) = gamma0PrimitivePhysicalTest N r n ρ x) := by
  have hq : 0 < |cuspFourierFrequency 1 n| :=
    abs_pos.mpr (cuspFourierFrequency_ne_zero 1 zero_lt_one n hn)
  have hw : 0 < (gamma0CuspTrueWidth N r : ℝ) :=
    Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N r)
  obtain ⟨_,hRc,hRp⟩ := spectral_cusp_width_test_properties _ 0 hw ρ hρ.continuous hcρ hpρ
  simp only [zero_div] at hRp
  have hR : ContDiff ℝ ∞ (fun y => ρ ((gamma0CuspTrueWidth N r : ℝ)*y)) :=
    hρ.comp (contDiff_const.mul contDiff_id)
  obtain ⟨_,hgc,hgp⟩ := spectralKLHeightPhysicalTest_properties hq _ hR.continuous hRc hRp
  exact ⟨spectralKLHeightPhysicalTest_contDiff hq _ hR hRc hRp,hgc,hgp,
    fun x => spectralKLHeightPhysicalTest_conj _ _ x⟩

theorem gamma0ABLRegular_native_window_action (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (n : ℤ) (hn : n ≠ 0) (Y : ℝ) (hY : 0 < Y)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) (hsρ : tsupport ρ ⊆ Ioi Y)
    (T ε : ℝ) (hT : 0 < T) :
    let F := spectralABLRegularCorrectedProfile T ε (gamma0PrimitivePhysicalTest N r n ρ)
    ∃ P : SpectralDecayingHeightProfile,
      P.exponent = 5/4 ∧
      (∀ y : ℝ, P.value y = Real.sqrt (y/(gamma0CuspTrueWidth N r : ℝ))*
        (F ((|cuspFourierFrequency 1 n|/(gamma0CuspTrueWidth N r : ℝ))*y)).re) ∧
      gamma0PrimitivePhysicalTest N r n P.value = F ∧
      gamma0PrimitiveDecayingPoincare N r n P =
        gamma0AmbientTestOperator N
          (spectralABLRegularEnergyTest T (T^(1-ε)) hT (Real.rpow_pos_of_pos hT _))
          (gamma0PrimitiveFourierPoincareTest N r n ρ hρ hcρ hpρ) ∧
      gamma0AmbientTestOperator N (spectralABLLiteralRegularEnergyTest T ε hT)
        (gamma0PrimitiveFourierPoincareTest N r n ρ hρ hcρ hpρ) =
          (1/4 : ℂ) • gamma0PrimitiveDecayingPoincare N r n P := by
  let g := gamma0PrimitivePhysicalTest N r n ρ
  let F := spectralABLRegularCorrectedProfile T ε g
  obtain ⟨hg,hgc,hgp,hgr⟩ := gamma0PrimitivePhysicalTest_properties N r n hn ρ hρ hcρ hpρ
  obtain ⟨_,_,⟨C,hC,hsmall,hlarge⟩,htrans⟩ :=
    spectralABLRegularCorrectedProfile_properties T ε hT g hg hgc hgp
  have hzero (x : ℝ) (hx : x ≤ 0) : F x = 0 := by
    simp [F,spectralABLRegularCorrectedProfile,spectralKLWindowSynthesis,not_lt.mpr hx]
  have hline (t : ℝ) : spectralABLRegularCorrected T (T^(1-ε)) (t : ℂ) =
      spectralContinuousTestSymbol
        (spectralABLRegularEnergyTest T (T^(1-ε)) hT (Real.rpow_pos_of_pos hT _)) t := by
    rw [spectralABLRegularCorrected_real,spectralABLRegularEnergyTest_continuous_symbol]
  have hb := spectralABLRegularCorrected_real_bound T (T^(1-ε)) hT (Real.rpow_pos_of_pos hT _)
  have hB : 0 ≤ spectralABLRegularBound T (T^(1-ε)) := (norm_nonneg _).trans (hb 0)
  have hF : ContDiffOn ℝ ∞ F (Ioi (0 : ℝ)) :=
    spectralKLWindowSynthesis_contDiffOn _ g
      (spectralABLRegularCorrected_real_contDiff T (T^(1-ε))).continuous hg hgc hgp _ hB
      (fun t => (hb t).trans (le_mul_of_one_le_right hB (by nlinarith [sq_nonneg t])))
  obtain ⟨P,hP,hvalue,hphysical,hact⟩ := gamma0Primitive_physical_window_action N r n hn Y hY
    ρ hρ hcρ hpρ hsρ F hF
    hzero (fun x _ => spectralABLRegularCorrectedProfile_real T ε g hgp hgr x)
    C hC hsmall hlarge (spectralABLRegularCorrected T (T^(1-ε)))
    (spectralABLRegularEnergyTest T (T^(1-ε)) hT (Real.rpow_pos_of_pos hT _))
    (spectralABLRegularEnergyTest_real _ _ _ _)
    (fun l => (spectralABLRegularEnergyTest_order _ _ _ _ l).symm) hline htrans
  refine ⟨P,hP,hvalue,gamma0PrimitivePhysicalTest_eq N r n hn P.value F hzero hphysical,hact,?_⟩
  change gamma0AmbientTestOperator N
    ((1/4 : ℂ) • spectralABLRegularEnergyTest T (T^(1-ε)) hT (Real.rpow_pos_of_pos hT _)) _ = _
  rw [gamma0AmbientTestOperator_smul,← hact]

theorem gamma0ABLExceptional_native_window_action (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (n : ℤ) (hn : n ≠ 0) (Y : ℝ) (hY : 0 < Y)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) (hsρ : tsupport ρ ⊆ Ioi Y)
    (a : ℝ) (A : ℕ) (hA : 1 ≤ A) :
    let F := spectralABLExceptionalCorrectedProfile a A (gamma0PrimitivePhysicalTest N r n ρ)
    ∃ P : SpectralDecayingHeightProfile,
      P.exponent = 5/4 ∧
      (∀ y : ℝ, P.value y = Real.sqrt (y/(gamma0CuspTrueWidth N r : ℝ))*
        (F ((|cuspFourierFrequency 1 n|/(gamma0CuspTrueWidth N r : ℝ))*y)).re) ∧
      gamma0PrimitivePhysicalTest N r n P.value = F ∧
      gamma0PrimitiveDecayingPoincare N r n P =
        gamma0AmbientTestOperator N (spectralABLExceptionalEnergyTest a A hA)
          (gamma0PrimitiveFourierPoincareTest N r n ρ hρ hcρ hpρ) ∧
      gamma0AmbientTestOperator N (spectralABLLiteralExceptionalEnergyTest a A hA)
        (gamma0PrimitiveFourierPoincareTest N r n ρ hρ hcρ hpρ) =
          (1/4 : ℂ) • gamma0PrimitiveDecayingPoincare N r n P := by
  let g := gamma0PrimitivePhysicalTest N r n ρ
  let F := spectralABLExceptionalCorrectedProfile a A g
  obtain ⟨hg,hgc,hgp,hgr⟩ := gamma0PrimitivePhysicalTest_properties N r n hn ρ hρ hcρ hpρ
  obtain ⟨_,_,⟨C,hC,hsmall,hlarge⟩,htrans⟩ :=
    spectralABLExceptionalCorrectedProfile_properties a A hA g hg hgc hgp
  have hzero (x : ℝ) (hx : x ≤ 0) : F x = 0 := by
    simp [F,spectralABLExceptionalCorrectedProfile,spectralKLWindowSynthesis,not_lt.mpr hx]
  have hline (t : ℝ) : spectralABLExceptionalCorrected a A (t : ℂ) =
      spectralContinuousTestSymbol (spectralABLExceptionalEnergyTest a A hA) t := by
    rw [spectralABLExceptionalCorrected_real,spectralABLExceptionalEnergyTest_continuous_symbol]
  have hb := spectralABLExceptionalCorrected_real_bound a hA
  have hB : 0 ≤ spectralABLExceptionalBound A := (norm_nonneg _).trans (hb 0)
  have hF : ContDiffOn ℝ ∞ F (Ioi (0 : ℝ)) :=
    spectralKLWindowSynthesis_contDiffOn _ g
      (spectralABLExceptionalCorrected_real_contDiff a hA).continuous hg hgc hgp _ hB
      (fun t => (hb t).trans (le_mul_of_one_le_right hB (by nlinarith [sq_nonneg t])))
  obtain ⟨P,hP,hvalue,hphysical,hact⟩ := gamma0Primitive_physical_window_action N r n hn Y hY
    ρ hρ hcρ hpρ hsρ F hF
    hzero (fun x _ => spectralABLExceptionalCorrectedProfile_real a A g hgp hgr x)
    C hC hsmall hlarge (spectralABLExceptionalCorrected a A)
    (spectralABLExceptionalEnergyTest a A hA)
    (spectralABLExceptionalEnergyTest_real _ _ _)
    (fun l => (spectralABLExceptionalEnergyTest_order _ _ _ l).symm) hline htrans
  refine ⟨P,hP,hvalue,gamma0PrimitivePhysicalTest_eq N r n hn P.value F hzero hphysical,hact,?_⟩
  change gamma0AmbientTestOperator N ((1/4 : ℂ) • spectralABLExceptionalEnergyTest a A hA) _ = _
  rw [gamma0AmbientTestOperator_smul,← hact]

end ArtinMatthews
