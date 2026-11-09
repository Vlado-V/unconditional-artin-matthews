module

public import ArtinMatthews.SpectralTrueWidthModulusLimit
public import ArtinMatthews.SpectralPrimitiveOrbitalPairing


set_option backward.privateInPublic true
@[expose] public section

/-! The absolutely summable physical fibres agree with the previously
proved genuine compact geometric fibres, in the same true-width coordinates. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups
namespace ArtinMatthews

theorem spectralWeylPhysicalBilinear_integer_sign {X : ℝ} (hX : 0 < X)
    (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (f g : ℝ → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (hfp : tsupport f ⊆ Ioi (0 : ℝ)) (hg : Continuous g)
    (hgc : HasCompactSupport g) (hgp : tsupport g ⊆ Ioi (0 : ℝ)) :
    spectralWeylPhysicalBilinear
      (cuspFourierFrequency 1 m/|cuspFourierFrequency 1 m|)
      (cuspFourierFrequency 1 n/|cuspFourierFrequency 1 n|) f g X =
      ∫ v, spectralWeylIntegerSignMultiplier m n v X*spectralKLPhysicalAnalysisIntegral f v*
        star (spectralKLPhysicalAnalysisIntegral g v) ∂spectralKLSpectralMeasure := by
  have hu := cuspFourierFrequency_ne_zero 1 zero_lt_one m hm
  have hv := cuspFourierFrequency_ne_zero 1 zero_lt_one n hn
  have hs := spectralWeyl_frequency_sign_sq hu
  have ht := spectralWeyl_frequency_sign_sq hv
  have he := spectralWeyl_frequency_sign_product hu hv
  have hpos := spectralWeyl_cusp_frequency_product_pos zero_lt_one m n
  by_cases hp : 0 < m*n
  · have hp' : 0 < cuspFourierFrequency 1 m*cuspFourierFrequency 1 n := hpos.mpr hp
    rw [ite_eq_left hp'] at he
    rw [spectralWeylPhysicalBilinear_same_J hX _ _ hs ht he f g hf hfc hfp hg hgc hgp]
    simp only [spectralWeylIntegerSignMultiplier,ite_eq_left hp]
  · have hp' : ¬ 0 < cuspFourierFrequency 1 m*cuspFourierFrequency 1 n := fun h => hp (hpos.mp h)
    rw [ite_eq_right hp'] at he
    rw [spectralWeylPhysicalBilinear_opposite_K hX _ _ hs ht he f g hf hfc hfp hg hgc hgp]
    simp only [spectralWeylIntegerSignMultiplier,ite_eq_right hp]

theorem gamma0PrimitivePositiveBesselFibre_eq_physical (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (c : Ioi (0 : ℕ)) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (ρ η : ℝ → ℝ) (hρ : Continuous ρ) (hη : Continuous η)
    (hcρ : HasCompactSupport ρ) (hcη : HasCompactSupport η)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) (hpη : tsupport η ⊆ Ioi (0 : ℝ)) :
    gamma0PrimitivePositiveBesselFibre N r s c m n ρ η =
      gamma0TrueWidthPhysicalFibre N r s c m n
        (spectralKLHeightPhysicalTest |cuspFourierFrequency 1 n|
          (fun y => η ((gamma0CuspTrueWidth N s : ℝ)*y)))
        (spectralKLHeightPhysicalTest |cuspFourierFrequency 1 m|
          (fun y => ρ ((gamma0CuspTrueWidth N r : ℝ)*y))) := by
  let _ : NeZero c.val := ⟨c.property.ne'⟩
  have ha : 0 < |cuspFourierFrequency 1 m| :=
    abs_pos.mpr (cuspFourierFrequency_ne_zero 1 zero_lt_one m hm)
  have hb : 0 < |cuspFourierFrequency 1 n| :=
    abs_pos.mpr (cuspFourierFrequency_ne_zero 1 zero_lt_one n hn)
  have hC := gamma0TrueWidthModulus_pos N r s (Nat.cast_pos.mpr c.property)
  have hr : 0 < (gamma0CuspTrueWidth N r : ℝ) := Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N r)
  have hs : 0 < (gamma0CuspTrueWidth N s : ℝ) := Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N s)
  obtain ⟨hR,hRc,hRp⟩ := spectral_cusp_width_test_properties _ 0 hr ρ hρ hcρ hpρ
  obtain ⟨hE,hEc,hEp⟩ := spectral_cusp_width_test_properties _ 0 hs η hη hcη hpη
  simp only [zero_div] at hRp hEp
  obtain ⟨hf,hfc,hfp⟩ := spectralKLHeightPhysicalTest_properties hb _ hE hEc hEp
  obtain ⟨hg,hgc,hgp⟩ := spectralKLHeightPhysicalTest_properties ha _ hR hRc hRp
  have he := spectralWeylPhysicalBilinear_integer_sign (by positivity :
      0 < Real.sqrt (|cuspFourierFrequency 1 m| * |cuspFourierFrequency 1 n|)*
        (2/gamma0TrueWidthModulus N r s (c.val : ℝ)))
    m n hm hn _ _ hf hfc hfp hg hgc hgp
  unfold gamma0PrimitivePositiveBesselFibre gamma0TrueWidthBesselOrbital gamma0TrueWidthPhysicalFibre
  dsimp only
  rw [he]
  ring

end ArtinMatthews
