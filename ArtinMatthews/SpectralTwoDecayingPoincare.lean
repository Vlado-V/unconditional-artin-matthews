module

public import ArtinMatthews.SpectralTrueWidthTwoProfileLimit
public import ArtinMatthews.SpectralDecayingHeightPairing
public import ArtinMatthews.SpectralDecayingMixedPhysicalPairing
public import ArtinMatthews.SpectralABLNativeWindowAction


set_option backward.privateInPublic true
@[expose] public section

/-! Both arguments in the actual primitive Poincare pairing may be
noncompact. The second cutoff is removed through a uniform modulus sum. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology MatrixGroups ContDiff InnerProductSpace
namespace ArtinMatthews

theorem gamma0PrimitivePhysicalTest_decaying_measurable (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (n : ℤ) (hn : n ≠ 0) (P : SpectralDecayingHeightProfile) :
    Measurable (gamma0PrimitivePhysicalTest N r n P.value) :=
  spectralKLHeightPhysicalTest_width_measurable
    (abs_pos.mpr (cuspFourierFrequency_ne_zero 1 zero_lt_one n hn))
    (Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N r)) P.value P.smooth.continuousOn

theorem gamma0TwoDecayingPoincare_inequivalent_physical (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (hneq : ¬ gamma0EisensteinCuspsEquivalent N r s)
    (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (P Q : SpectralDecayingHeightProfile) (hQ : Q.exponent ≤ 3/2)
    {B M : ℝ} (hB : 1/2 < B) (hB₁ : B ≤ 1) (hM : 0 ≤ M)
    (hMoment : Integrable (fun x : ℝ => x^(-B)*‖gamma0PrimitivePhysicalTest N r m P.value x‖)
      spectralKLPhysicalMeasure)
    (hf : ∀ x, 0 < x → ‖gamma0PrimitivePhysicalTest N s n Q.value x‖ ≤ M*x^B) :
    inner ℂ (gamma0PrimitiveDecayingPoincare N r m P) (gamma0PrimitiveDecayingPoincare N s n Q) =
      ∑' c : Ioi (0 : ℕ), gamma0TrueWidthPhysicalFibre N r s c m n
        (gamma0PrimitivePhysicalTest N s n Q.value) (gamma0PrimitivePhysicalTest N r m P.value) := by
  let f := gamma0PrimitivePhysicalTest N s n Q.value
  let g := gamma0PrimitivePhysicalTest N r m P.value
  let A (K : ℕ) := gamma0PrimitiveFourierPoincareTest N r m (spectralHeightProfilePartial K P.value)
    (spectralHeightProfilePartial_contDiff K P.value P.smooth)
    (spectralHeightProfilePartial_compact K P.value)
    (spectralHeightProfilePartial_positive K P.value)
  have hq : 0 < |cuspFourierFrequency 1 m| :=
    abs_pos.mpr (cuspFourierFrequency_ne_zero 1 zero_lt_one m hm)
  have hw : 0 < (gamma0CuspTrueWidth N r : ℝ) := Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N r)
  have hs := gamma0TrueWidthPhysicalSeries_cutoff_right_tendsto N r s m n hm hn (div_pos hw hq)
    hB hB₁ hM f g (gamma0PrimitivePhysicalTest_decaying_measurable N s n hn Q)
    (gamma0PrimitivePhysicalTest_decaying_measurable N r m hm P) hMoment hf
  have hA : Tendsto A atTop (𝓝 (gamma0PrimitiveDecayingPoincare N r m P)) :=
    gamma0PrimitiveDecayingPoincare_partial_tendsto N r m P
  have hi : Tendsto (fun K : ℕ => inner ℂ (A K) (gamma0PrimitiveDecayingPoincare N s n Q))
      atTop (𝓝 (inner ℂ (gamma0PrimitiveDecayingPoincare N r m P)
        (gamma0PrimitiveDecayingPoincare N s n Q))) :=
    ((continuous_id.inner continuous_const).tendsto
      (gamma0PrimitiveDecayingPoincare N r m P)).comp hA
  have he (K : ℕ) : inner ℂ (A K) (gamma0PrimitiveDecayingPoincare N s n Q) =
      ∑' c : Ioi (0 : ℕ), gamma0TrueWidthPhysicalFibre N r s c m n f
        (spectralWeylProfileCutoff ((gamma0CuspTrueWidth N r : ℝ)/|cuspFourierFrequency 1 m|) K g) := by
    rw [gamma0PrimitiveDecayingPoincare_inequivalent_physical N r s hneq m n hm hn
      (spectralHeightProfilePartial K P.value)
      (spectralHeightProfilePartial_contDiff K P.value P.smooth)
      (spectralHeightProfilePartial_compact K P.value)
      (spectralHeightProfilePartial_positive K P.value) Q hQ]
    simp_rw [spectralKLHeightPhysicalTest_partial_width]
    rfl
  rw [funext he] at hi
  exact tendsto_nhds_unique hi hs

theorem gamma0TwoDecayingPoincare_sameCusp_physical (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (P Q : SpectralDecayingHeightProfile) (hQ : Q.exponent ≤ 3/2)
    {B M : ℝ} (hB : 1/2 < B) (hB₁ : B ≤ 1) (hM : 0 ≤ M)
    (hMoment : Integrable (fun x : ℝ => x^(-B)*‖gamma0PrimitivePhysicalTest N r m P.value x‖)
      spectralKLPhysicalMeasure)
    (hf : ∀ x, 0 < x → ‖gamma0PrimitivePhysicalTest N r n Q.value x‖ ≤ M*x^B) :
    inner ℂ (gamma0PrimitiveDecayingPoincare N r m P) (gamma0PrimitiveDecayingPoincare N r n Q) =
      (if m = n then (gamma0CuspTrueWidth N r : ℂ)*(cuspFourierHeightPairing P.value Q.value : ℂ) else 0) +
      ∑' c : Ioi (0 : ℕ), gamma0TrueWidthPhysicalFibre N r r c m n
        (gamma0PrimitivePhysicalTest N r n Q.value) (gamma0PrimitivePhysicalTest N r m P.value) := by
  let f := gamma0PrimitivePhysicalTest N r n Q.value
  let g := gamma0PrimitivePhysicalTest N r m P.value
  let A (K : ℕ) := gamma0PrimitiveFourierPoincareTest N r m (spectralHeightProfilePartial K P.value)
    (spectralHeightProfilePartial_contDiff K P.value P.smooth)
    (spectralHeightProfilePartial_compact K P.value)
    (spectralHeightProfilePartial_positive K P.value)
  let z (K : ℕ) : ℂ := if m = n then (gamma0CuspTrueWidth N r : ℂ)*
    (cuspFourierHeightPairing (spectralHeightProfilePartial K P.value) Q.value : ℂ) else 0
  let zLimit : ℂ := if m = n then (gamma0CuspTrueWidth N r : ℂ)*
    (cuspFourierHeightPairing P.value Q.value : ℂ) else 0
  have hq : 0 < |cuspFourierFrequency 1 m| :=
    abs_pos.mpr (cuspFourierFrequency_ne_zero 1 zero_lt_one m hm)
  have hw : 0 < (gamma0CuspTrueWidth N r : ℝ) := Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N r)
  have hs := gamma0TrueWidthPhysicalSeries_cutoff_right_tendsto N r r m n hm hn (div_pos hw hq)
    hB hB₁ hM f g (gamma0PrimitivePhysicalTest_decaying_measurable N r n hn Q)
    (gamma0PrimitivePhysicalTest_decaying_measurable N r m hm P) hMoment hf
  have hz : Tendsto z atTop (𝓝 zLimit) := by
    by_cases hmn : m = n
    · simp only [z,zLimit,ite_eq_left hmn]
      exact tendsto_const_nhds.mul
        (Complex.continuous_ofReal.continuousAt.tendsto.comp (spectralDecayingHeightPairing_cutoff_tendsto P Q))
    · simp only [z,zLimit,ite_eq_right hmn]
      exact tendsto_const_nhds
  have hA : Tendsto A atTop (𝓝 (gamma0PrimitiveDecayingPoincare N r m P)) :=
    gamma0PrimitiveDecayingPoincare_partial_tendsto N r m P
  have hi : Tendsto (fun K : ℕ => inner ℂ (A K) (gamma0PrimitiveDecayingPoincare N r n Q))
      atTop (𝓝 (inner ℂ (gamma0PrimitiveDecayingPoincare N r m P)
        (gamma0PrimitiveDecayingPoincare N r n Q))) :=
    ((continuous_id.inner continuous_const).tendsto
      (gamma0PrimitiveDecayingPoincare N r m P)).comp hA
  have he (K : ℕ) : inner ℂ (A K) (gamma0PrimitiveDecayingPoincare N r n Q) = z K +
      ∑' c : Ioi (0 : ℕ), gamma0TrueWidthPhysicalFibre N r r c m n f
        (spectralWeylProfileCutoff ((gamma0CuspTrueWidth N r : ℝ)/|cuspFourierFrequency 1 m|) K g) := by
    rw [gamma0PrimitiveDecayingPoincare_sameCusp_physical N r m n hm hn
      (spectralHeightProfilePartial K P.value)
      (spectralHeightProfilePartial_contDiff K P.value P.smooth)
      (spectralHeightProfilePartial_compact K P.value)
      (spectralHeightProfilePartial_positive K P.value) Q hQ]
    simp_rw [spectralKLHeightPhysicalTest_partial_width]
    rfl
  rw [funext he] at hi
  exact tendsto_nhds_unique hi (hz.add hs)

end ArtinMatthews
