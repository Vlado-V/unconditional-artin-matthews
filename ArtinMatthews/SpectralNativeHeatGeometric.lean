module

public import ArtinMatthews.SpectralNativeHeatAction
public import ArtinMatthews.SpectralNativeHeatMoment
public import ArtinMatthews.SpectralTwoDecayingPoincare


set_option backward.privateInPublic true
@[expose] public section

/-! Actual Gaussian-regularized geometric identities for the literal
source windows, without a compact height-test factor. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups ContDiff InnerProductSpace
namespace ArtinMatthews

theorem gamma0HeatRegular_sameCusp_geometric (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (T ε R : ℝ) (hT : 0 < T) (hR : 0 < R) :
    let F := spectralKLHeatProfile R
    let G := spectralABLRegularHeatProfile T ε R
    inner ℂ (gamma0HeatPoincareTest N r m hm R hR)
      (gamma0AmbientTestOperator N (spectralABLLiteralRegularEnergyTest T ε hT) (gamma0HeatPoincareTest N r n hn R hR)) =
      (1/4 : ℂ)*((if m = n then (gamma0CuspTrueWidth N r : ℂ)*
        (cuspFourierHeightPairing
          (fun y => Real.sqrt (y/(gamma0CuspTrueWidth N r : ℝ))*
            (F ((|cuspFourierFrequency 1 m|/(gamma0CuspTrueWidth N r : ℝ))*y)).re)
          (fun y => Real.sqrt (y/(gamma0CuspTrueWidth N r : ℝ))*
            (G ((|cuspFourierFrequency 1 n|/(gamma0CuspTrueWidth N r : ℝ))*y)).re) : ℂ)
        else 0) +
        ∑' c : Ioi (0 : ℕ), gamma0TrueWidthPhysicalFibre N r r c m n G F) := by
  dsimp only
  let P := gamma0HeatHeightProfile N r m hm R hR
  obtain ⟨Q,hQ,hvalue,hphysical,_,hact⟩ := gamma0HeatPoincareTest_regular_action N r n hn T ε R hT hR
  have hF := spectralKLHeatRegularity_five_eighths _ (spectralKLHeatProfile_properties R hR)
    (spectralKLHeatProfile_nonpositive_zero R)
  have hMoment : Integrable
      (fun x : ℝ => x^(-(5/8 : ℝ))*‖gamma0PrimitivePhysicalTest N r m P.value x‖) spectralKLPhysicalMeasure := by
    simpa only [P,gamma0HeatHeightProfile_physical] using hF.1
  obtain ⟨M,hM,hpower⟩ := (spectralKLHeatRegularity_five_eighths _
    (spectralABLRegularHeatProfile_properties T ε R hT hR)
    (spectralABLRegularHeatProfile_nonpositive_zero T ε R)).2
  have hQpower : ∀ x : ℝ, 0 < x → ‖gamma0PrimitivePhysicalTest N r n Q.value x‖ ≤ M*x^(5/8 : ℝ) := by
    simpa only [hphysical] using hpower
  have hgeom := gamma0TwoDecayingPoincare_sameCusp_physical N r m n hm hn P Q
    (by rw [hQ]; norm_num) (B := (5/8 : ℝ)) (by norm_num) (by norm_num) hM hMoment hQpower
  rw [hact,inner_smul_right]
  change (1/4 : ℂ)*inner ℂ (gamma0PrimitiveDecayingPoincare N r m P)
    (gamma0PrimitiveDecayingPoincare N r n Q) = _
  rw [hgeom,hphysical]
  dsimp only [P]
  rw [gamma0HeatHeightProfile_physical,funext hvalue,
    funext (gamma0HeatHeightProfile_value N r m hm R hR)]

theorem gamma0HeatRegular_inequivalent_geometric (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (hneq : ¬ gamma0EisensteinCuspsEquivalent N r s) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (T ε R : ℝ) (hT : 0 < T) (hR : 0 < R) :
    let F := spectralKLHeatProfile R
    let G := spectralABLRegularHeatProfile T ε R
    inner ℂ (gamma0HeatPoincareTest N r m hm R hR)
      (gamma0AmbientTestOperator N (spectralABLLiteralRegularEnergyTest T ε hT) (gamma0HeatPoincareTest N s n hn R hR)) =
      (1/4 : ℂ)*(∑' c : Ioi (0 : ℕ), gamma0TrueWidthPhysicalFibre N r s c m n G F) := by
  dsimp only
  let P := gamma0HeatHeightProfile N r m hm R hR
  obtain ⟨Q,hQ,_,hphysical,_,hact⟩ := gamma0HeatPoincareTest_regular_action N s n hn T ε R hT hR
  have hF := spectralKLHeatRegularity_five_eighths _ (spectralKLHeatProfile_properties R hR)
    (spectralKLHeatProfile_nonpositive_zero R)
  have hMoment : Integrable
      (fun x : ℝ => x^(-(5/8 : ℝ))*‖gamma0PrimitivePhysicalTest N r m P.value x‖) spectralKLPhysicalMeasure := by
    simpa only [P,gamma0HeatHeightProfile_physical] using hF.1
  obtain ⟨M,hM,hpower⟩ := (spectralKLHeatRegularity_five_eighths _
    (spectralABLRegularHeatProfile_properties T ε R hT hR)
    (spectralABLRegularHeatProfile_nonpositive_zero T ε R)).2
  have hQpower : ∀ x : ℝ, 0 < x → ‖gamma0PrimitivePhysicalTest N s n Q.value x‖ ≤ M*x^(5/8 : ℝ) := by
    simpa only [hphysical] using hpower
  have hgeom := gamma0TwoDecayingPoincare_inequivalent_physical N r s hneq m n hm hn P Q
    (by rw [hQ]; norm_num) (B := (5/8 : ℝ)) (by norm_num) (by norm_num) hM hMoment hQpower
  rw [hact,inner_smul_right]
  change (1/4 : ℂ)*inner ℂ (gamma0PrimitiveDecayingPoincare N r m P)
    (gamma0PrimitiveDecayingPoincare N s n Q) = _
  rw [hgeom,hphysical]
  dsimp only [P]
  rw [gamma0HeatHeightProfile_physical]

theorem gamma0HeatExceptional_sameCusp_geometric (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (a : ℝ) (A : ℕ) (R : ℝ) (hA : 1 ≤ A) (hR : 0 < R) :
    let F := spectralKLHeatProfile R
    let G := spectralABLExceptionalHeatProfile a A R
    inner ℂ (gamma0HeatPoincareTest N r m hm R hR)
      (gamma0AmbientTestOperator N (spectralABLLiteralExceptionalEnergyTest a A hA) (gamma0HeatPoincareTest N r n hn R hR)) =
      (1/4 : ℂ)*((if m = n then (gamma0CuspTrueWidth N r : ℂ)*
        (cuspFourierHeightPairing
          (fun y => Real.sqrt (y/(gamma0CuspTrueWidth N r : ℝ))*
            (F ((|cuspFourierFrequency 1 m|/(gamma0CuspTrueWidth N r : ℝ))*y)).re)
          (fun y => Real.sqrt (y/(gamma0CuspTrueWidth N r : ℝ))*
            (G ((|cuspFourierFrequency 1 n|/(gamma0CuspTrueWidth N r : ℝ))*y)).re) : ℂ)
        else 0) +
        ∑' c : Ioi (0 : ℕ), gamma0TrueWidthPhysicalFibre N r r c m n G F) := by
  dsimp only
  let P := gamma0HeatHeightProfile N r m hm R hR
  obtain ⟨Q,hQ,hvalue,hphysical,_,hact⟩ := gamma0HeatPoincareTest_exceptional_action N r n hn a A R hA hR
  have hF := spectralKLHeatRegularity_five_eighths _ (spectralKLHeatProfile_properties R hR)
    (spectralKLHeatProfile_nonpositive_zero R)
  have hMoment : Integrable
      (fun x : ℝ => x^(-(5/8 : ℝ))*‖gamma0PrimitivePhysicalTest N r m P.value x‖) spectralKLPhysicalMeasure := by
    simpa only [P,gamma0HeatHeightProfile_physical] using hF.1
  obtain ⟨M,hM,hpower⟩ := (spectralKLHeatRegularity_five_eighths _
    (spectralABLExceptionalHeatProfile_properties a A R hA hR)
    (spectralABLExceptionalHeatProfile_nonpositive_zero a A R)).2
  have hQpower : ∀ x : ℝ, 0 < x → ‖gamma0PrimitivePhysicalTest N r n Q.value x‖ ≤ M*x^(5/8 : ℝ) := by
    simpa only [hphysical] using hpower
  have hgeom := gamma0TwoDecayingPoincare_sameCusp_physical N r m n hm hn P Q
    (by rw [hQ]; norm_num) (B := (5/8 : ℝ)) (by norm_num) (by norm_num) hM hMoment hQpower
  rw [hact,inner_smul_right]
  change (1/4 : ℂ)*inner ℂ (gamma0PrimitiveDecayingPoincare N r m P)
    (gamma0PrimitiveDecayingPoincare N r n Q) = _
  rw [hgeom,hphysical]
  dsimp only [P]
  rw [gamma0HeatHeightProfile_physical,funext hvalue,
    funext (gamma0HeatHeightProfile_value N r m hm R hR)]

theorem gamma0HeatExceptional_inequivalent_geometric (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (hneq : ¬ gamma0EisensteinCuspsEquivalent N r s) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (a : ℝ) (A : ℕ) (R : ℝ) (hA : 1 ≤ A) (hR : 0 < R) :
    let F := spectralKLHeatProfile R
    let G := spectralABLExceptionalHeatProfile a A R
    inner ℂ (gamma0HeatPoincareTest N r m hm R hR)
      (gamma0AmbientTestOperator N (spectralABLLiteralExceptionalEnergyTest a A hA) (gamma0HeatPoincareTest N s n hn R hR)) =
      (1/4 : ℂ)*(∑' c : Ioi (0 : ℕ), gamma0TrueWidthPhysicalFibre N r s c m n G F) := by
  dsimp only
  let P := gamma0HeatHeightProfile N r m hm R hR
  obtain ⟨Q,hQ,_,hphysical,_,hact⟩ := gamma0HeatPoincareTest_exceptional_action N s n hn a A R hA hR
  have hF := spectralKLHeatRegularity_five_eighths _ (spectralKLHeatProfile_properties R hR)
    (spectralKLHeatProfile_nonpositive_zero R)
  have hMoment : Integrable
      (fun x : ℝ => x^(-(5/8 : ℝ))*‖gamma0PrimitivePhysicalTest N r m P.value x‖) spectralKLPhysicalMeasure := by
    simpa only [P,gamma0HeatHeightProfile_physical] using hF.1
  obtain ⟨M,hM,hpower⟩ := (spectralKLHeatRegularity_five_eighths _
    (spectralABLExceptionalHeatProfile_properties a A R hA hR)
    (spectralABLExceptionalHeatProfile_nonpositive_zero a A R)).2
  have hQpower : ∀ x : ℝ, 0 < x → ‖gamma0PrimitivePhysicalTest N s n Q.value x‖ ≤ M*x^(5/8 : ℝ) := by
    simpa only [hphysical] using hpower
  have hgeom := gamma0TwoDecayingPoincare_inequivalent_physical N r s hneq m n hm hn P Q
    (by rw [hQ]; norm_num) (B := (5/8 : ℝ)) (by norm_num) (by norm_num) hM hMoment hQpower
  rw [hact,inner_smul_right]
  change (1/4 : ℂ)*inner ℂ (gamma0PrimitiveDecayingPoincare N r m P)
    (gamma0PrimitiveDecayingPoincare N s n Q) = _
  rw [hgeom,hphysical]
  dsimp only [P]
  rw [gamma0HeatHeightProfile_physical]

end ArtinMatthews
