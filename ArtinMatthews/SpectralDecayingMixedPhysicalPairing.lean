module

public import ArtinMatthews.SpectralDecayingPhysicalPairing
public import ArtinMatthews.SpectralInequivalentCuspZero


set_option backward.privateInPublic true
@[expose] public section

/-! The actual noncompact geometric pairing for inequivalent cusps.
The zero sector vanishes by the proved cusp correspondence criterion. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology MatrixGroups ContDiff InnerProductSpace
namespace ArtinMatthews

theorem gamma0PrimitiveFourierPoincareTest_inequivalent_physical (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (hneq : ¬ gamma0EisensteinCuspsEquivalent N r s)
    (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (ρ η : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hη : ContDiff ℝ ∞ η)
    (hcρ : HasCompactSupport ρ) (hcη : HasCompactSupport η)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) (hpη : tsupport η ⊆ Ioi (0 : ℝ)) :
    inner ℂ (gamma0PrimitiveFourierPoincareTest N r m ρ hρ hcρ hpρ)
      (gamma0PrimitiveFourierPoincareTest N s n η hη hcη hpη) =
      ∑' c : Ioi (0 : ℕ), gamma0TrueWidthPhysicalFibre N r s c m n
        (spectralKLHeightPhysicalTest |cuspFourierFrequency 1 n|
          (fun y => η ((gamma0CuspTrueWidth N s : ℝ)*y)))
        (spectralKLHeightPhysicalTest |cuspFourierFrequency 1 m|
          (fun y => ρ ((gamma0CuspTrueWidth N r : ℝ)*y))) := by
  rw [gamma0PrimitiveFourierPoincareTest_physical N r s m n hm hn ρ η hρ hη hcρ hcη hpρ hpη,
    gamma0ZeroGeometricSum_eq_zero_of_inequivalent N r s hneq]
  simp only [mul_zero,zero_add]

theorem gamma0PrimitiveDecayingPoincare_inequivalent_physical (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (hneq : ¬ gamma0EisensteinCuspsEquivalent N r s)
    (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) (P : SpectralDecayingHeightProfile)
    (hP : P.exponent ≤ 3/2) :
    inner ℂ (gamma0PrimitiveFourierPoincareTest N r m ρ hρ hcρ hpρ)
      (gamma0PrimitiveDecayingPoincare N s n P) =
      ∑' c : Ioi (0 : ℕ), gamma0TrueWidthPhysicalFibre N r s c m n
        (spectralKLHeightPhysicalTest |cuspFourierFrequency 1 n|
          (fun y => P.value ((gamma0CuspTrueWidth N s : ℝ)*y)))
        (spectralKLHeightPhysicalTest |cuspFourierFrequency 1 m|
          (fun y => ρ ((gamma0CuspTrueWidth N r : ℝ)*y))) := by
  let q := |cuspFourierFrequency 1 n|
  let w := (gamma0CuspTrueWidth N s : ℝ)
  let f := spectralKLHeightPhysicalTest q (fun y => P.value (w*y))
  let g := spectralKLHeightPhysicalTest |cuspFourierFrequency 1 m|
    (fun y => ρ ((gamma0CuspTrueWidth N r : ℝ)*y))
  let H (K : ℕ) := gamma0PrimitiveFourierPoincareTest N s n
    (spectralHeightProfilePartial K P.value)
    (spectralHeightProfilePartial_contDiff K P.value P.smooth)
    (spectralHeightProfilePartial_compact K P.value)
    (spectralHeightProfilePartial_positive K P.value)
  have hq : 0 < q := abs_pos.mpr (cuspFourierFrequency_ne_zero 1 zero_lt_one n hn)
  have hw : 0 < w := Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N s)
  have ha : 0 < w/q := div_pos hw hq
  have hf : Measurable f := spectralKLHeightPhysicalTest_width_measurable hq hw P.value P.smooth.continuousOn
  have hb : ∀ x, 0 < x → ‖f x‖ ≤
      (P.bound*w^P.exponent/q^(P.exponent-1/2))*x^(P.exponent-1/2) :=
    fun _ hx => spectralKLHeightPhysicalTest_decaying_power hq hw P hx
  have hqa : 0 < |cuspFourierFrequency 1 m| :=
    abs_pos.mpr (cuspFourierFrequency_ne_zero 1 zero_lt_one m hm)
  have hwr : 0 < (gamma0CuspTrueWidth N r : ℝ) := Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N r)
  obtain ⟨hR,hRc,hRp⟩ := spectral_cusp_width_test_properties _ 0 hwr ρ hρ.continuous hcρ hpρ
  simp only [zero_div] at hRp
  obtain ⟨hg,hgc,hgp⟩ := spectralKLHeightPhysicalTest_properties hqa _ hR hRc hRp
  have hPb := P.bound_nonneg
  have hs := gamma0TrueWidthPhysicalSeries_cutoff_tendsto N r s m n hm hn ha
    (by linarith [P.exponent_gt_one] : 1/2 < P.exponent-1/2) (by linarith : P.exponent-1/2 ≤ 1)
    (by positivity : 0 ≤ P.bound*w^P.exponent/q^(P.exponent-1/2)) f g hf hg hgc hgp hb
  have hleft : Tendsto (fun K : ℕ => inner ℂ
      (gamma0PrimitiveFourierPoincareTest N r m ρ hρ hcρ hpρ) (H K)) atTop
      (𝓝 (inner ℂ (gamma0PrimitiveFourierPoincareTest N r m ρ hρ hcρ hpρ)
        (gamma0PrimitiveDecayingPoincare N s n P))) :=
    ((continuous_const.inner continuous_id).tendsto _).comp
      (gamma0PrimitiveDecayingPoincare_partial_tendsto N s n P)
  have he (K : ℕ) : inner ℂ (gamma0PrimitiveFourierPoincareTest N r m ρ hρ hcρ hpρ) (H K) =
      ∑' c : Ioi (0 : ℕ), gamma0TrueWidthPhysicalFibre N r s c m n
        (spectralWeylProfileCutoff (w/q) K f) g := by
    rw [gamma0PrimitiveFourierPoincareTest_inequivalent_physical N r s hneq m n hm hn ρ
      (spectralHeightProfilePartial K P.value) hρ (spectralHeightProfilePartial_contDiff K P.value P.smooth)
      hcρ (spectralHeightProfilePartial_compact K P.value) hpρ (spectralHeightProfilePartial_positive K P.value)]
    simp_rw [spectralKLHeightPhysicalTest_partial_width]
    rfl
  rw [funext he] at hleft
  exact tendsto_nhds_unique hleft hs

end ArtinMatthews
