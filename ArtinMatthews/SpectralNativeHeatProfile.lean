module

public import ArtinMatthews.SpectralComplexNativeProfileData
public import ArtinMatthews.SpectralNativePhysicalTransform
public import ArtinMatthews.SpectralKLHeatProfiles


set_option backward.privateInPublic true
@[expose] public section

/-! The actual inverse Gaussian KL profile defines a native Poincare
vector with its literal true-width and frequency normalization. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups ContDiff InnerProductSpace
namespace ArtinMatthews

theorem gamma0HeatRegularity_native_exists (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (n : ℤ) (hn : n ≠ 0) (F : ℝ → ℂ)
    (hreg : SpectralKLHeatRegularity F)
    (hzero : ∀ x : ℝ, x ≤ 0 → F x = 0)
    (hreal : ∀ x : ℝ, star (F x) = F x) :
    ∃ P : SpectralDecayingHeightProfile,
      P.exponent = 5/4 ∧
      (∀ y : ℝ, P.value y = Real.sqrt (y/(gamma0CuspTrueWidth N r : ℝ))*
        (F ((|cuspFourierFrequency 1 n|/(gamma0CuspTrueWidth N r : ℝ))*y)).re) ∧
      gamma0PrimitivePhysicalTest N r n P.value = F := by
  obtain ⟨hs,_,⟨C,hC,hsmall⟩,hlarge⟩ := hreg
  obtain ⟨D,_,hD⟩ := hlarge 2 (by norm_num)
  exact gamma0NativeComplexProfile_exists N r n hn F hs hzero (fun x _ => hreal x)
    C D hC hsmall hD

theorem gamma0HeatHeightProfile_exists (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (n : ℤ) (hn : n ≠ 0) (R : ℝ) (hR : 0 < R) :
    ∃ P : SpectralDecayingHeightProfile,
      P.exponent = 5/4 ∧
      (∀ y : ℝ, P.value y = Real.sqrt (y/(gamma0CuspTrueWidth N r : ℝ))*
        (spectralKLHeatProfile R ((|cuspFourierFrequency 1 n|/(gamma0CuspTrueWidth N r : ℝ))*y)).re) ∧
      gamma0PrimitivePhysicalTest N r n P.value = spectralKLHeatProfile R :=
  gamma0HeatRegularity_native_exists N r n hn _ (spectralKLHeatProfile_properties R hR)
    (spectralKLHeatProfile_nonpositive_zero R) (spectralKLHeatProfile_real R)

def gamma0HeatHeightProfile (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (n : ℤ) (hn : n ≠ 0) (R : ℝ) (hR : 0 < R) : SpectralDecayingHeightProfile :=
  Classical.choose (gamma0HeatHeightProfile_exists N r n hn R hR)

theorem gamma0HeatHeightProfile_exponent (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (n : ℤ) (hn : n ≠ 0) (R : ℝ) (hR : 0 < R) :
    (gamma0HeatHeightProfile N r n hn R hR).exponent = 5/4 :=
  (Classical.choose_spec (gamma0HeatHeightProfile_exists N r n hn R hR)).1

theorem gamma0HeatHeightProfile_value (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (n : ℤ) (hn : n ≠ 0) (R : ℝ) (hR : 0 < R) (y : ℝ) :
    (gamma0HeatHeightProfile N r n hn R hR).value y = Real.sqrt (y/(gamma0CuspTrueWidth N r : ℝ))*
      (spectralKLHeatProfile R ((|cuspFourierFrequency 1 n|/(gamma0CuspTrueWidth N r : ℝ))*y)).re :=
  (Classical.choose_spec (gamma0HeatHeightProfile_exists N r n hn R hR)).2.1 y

theorem gamma0HeatHeightProfile_physical (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (n : ℤ) (hn : n ≠ 0) (R : ℝ) (hR : 0 < R) :
    gamma0PrimitivePhysicalTest N r n (gamma0HeatHeightProfile N r n hn R hR).value =
      spectralKLHeatProfile R :=
  (Classical.choose_spec (gamma0HeatHeightProfile_exists N r n hn R hR)).2.2

def gamma0HeatPoincareTest (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (n : ℤ) (hn : n ≠ 0) (R : ℝ) (hR : 0 < R) : Gamma0RegionL2 N :=
  gamma0PrimitiveDecayingPoincare N r n (gamma0HeatHeightProfile N r n hn R hR)

theorem gamma0HeatPoincareTest_ambient_coefficient (N : ℕ) [NeZero N]
    (eig : ℝ) (heig : 0 ≤ eig) (v : Gamma0RegionL2 N)
    (hG : gamma0Green N v = (((eig+1)⁻¹ : ℝ) : ℂ) • v)
    (r : SL(2, ℤ)) (n : ℤ) (hn : n ≠ 0) (R : ℝ) (hR : 0 < R) :
    inner ℂ (gamma0HeatPoincareTest N r n hn R hR) v =
      (Real.sqrt (gamma0CuspTrueWidth N r : ℝ) : ℂ)*
        gamma0AmbientBesselAmplitude N eig heig v hG r
          ((gamma0CuspFrequencyStep N r : ℤ)*n) (gamma0CuspFrequencyStep_mul_ne_zero N r hn)*
        Complex.exp ((1/4-(eig : ℂ))/(R : ℂ)^2) := by
  let P := gamma0HeatHeightProfile N r n hn R hR
  let ν := Complex.sqrt (1/4-(eig : ℂ))
  let A := (Real.sqrt (gamma0CuspTrueWidth N r : ℝ) : ℂ)*
    gamma0AmbientBesselAmplitude N eig heig v hG r
      ((gamma0CuspFrequencyStep N r : ℤ)*n) (gamma0CuspFrequencyStep_mul_ne_zero N r hn)
  have h := gamma0PrimitiveDecayingPoincare_ambient_order_integral N eig heig v hG r n hn P
  change inner ℂ (gamma0HeatPoincareTest N r n hn R hR) v = A*gamma0NativeOrderTransform N r n P.value ν at h
  have he := gamma0NativeOrderTransform_eq_compactOrder N r n hn P.value ν
  change gamma0NativeOrderTransform N r n P.value ν =
    spectralKLCompactOrderTransform (gamma0PrimitivePhysicalTest N r n P.value) ν at he
  rw [show gamma0PrimitivePhysicalTest N r n P.value = spectralKLHeatProfile R from
    gamma0HeatHeightProfile_physical N r n hn R hR] at he
  rw [he,spectralKLHeatProfile_continued_transform R hR ν
    (spectralNonnegativeEnergy_order_abs_re_le eig heig)] at h
  simpa only [ν,spectralComplexSqrt_sq] using h

end ArtinMatthews
