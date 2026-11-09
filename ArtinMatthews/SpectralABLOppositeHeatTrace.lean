module

public import ArtinMatthews.SpectralABLOppositeModulus
public import ArtinMatthews.SpectralNativeHeatTrace


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set MeasureTheory
open scoped MatrixGroups ContDiff InnerProductSpace
noncomputable section

theorem spectralWeylOppositeHeat_physical (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ))
    {X : ℝ} (hX : 0 < X) (R : ℝ) (hR : 0 < R)
    (s t : ℝ) (hs : s^2 = 1) (ht : t^2 = 1) (hst : s*t = -1) :
    spectralWeylPhysicalBilinear s t
      (spectralKLWeightedHeatProfile (spectralABLOppositeFourierWeight f) R) (spectralKLHeatProfile R) X =
      ∫ u, spectralWeylKMultiplier u X*spectralABLOppositeFourierWeight f (u : ℂ)*
        Complex.exp (-2*((u : ℂ)/(R : ℂ))^2) ∂spectralKLSpectralMeasure := by
  let H := spectralABLOppositeFourierWeight f
  let F := spectralKLHeatProfile R
  let G := spectralKLWeightedHeatProfile H R
  obtain ⟨C,hC,hbound⟩ := spectralABLOppositeFourierWeight_strip_bound f hf hc hp
  have hS := spectralABLOppositeFourierWeight_real_smooth f hf.continuous hc hp
  have hF := spectralKLHeatProfile_properties R hR
  have hG := spectralKLWeightedHeatProfile_properties H R hR
    (spectralABLOppositeFourierWeight_even f hp) hS
    (fun z _ => spectralABLOppositeFourierWeight_entire f hf.continuous hc hp z) C hC hbound
  have hzF := spectralKLHeatProfile_nonpositive_zero R
  have hzG := spectralKLWeightedHeatProfile_nonpositive_zero H R
  have hmF := spectralKLHeatRegularity_measurable F hF hzF
  have hmG := spectralKLHeatRegularity_measurable G hG hzG
  obtain ⟨M,hM,hpower⟩ := (spectralKLHeatRegularity_five_eighths G hG hzG).2
  have hMoment := (spectralKLHeatRegularity_five_eighths F hF hzF).1
  have he := spectralWeylPhysicalBilinear_opposite_K_two_noncompact zero_lt_one hX
    (by norm_num : (0 : ℝ) < 5/8) (by norm_num : (5/8 : ℝ) ≤ 1) hM
    s t hs ht hst G F hmG hmF hG.1.continuousOn hF.1.continuousOn hG.2.1 hF.2.1 hMoment hpower
  change spectralWeylPhysicalBilinear s t G F X = _
  rw [he]
  apply integral_congr_ae
  filter_upwards [spectralKLWeightedHeatProfile_completed_analysis H R hR hS C hC hbound hG.2.1,
    spectralKLHeatProfile_completed_analysis R hR hF.2.1] with u hGu hFu
  rw [hGu,hFu,spectralKLGaussianWeightedData,spectralKLGaussianData_real_star]
  calc
    _ = spectralWeylKMultiplier u X*H (u : ℂ)*
        (spectralKLGaussianData R (u : ℂ)*spectralKLGaussianData R (u : ℂ)) := by ring
    _ = _ := by rw [spectralHeatGaussian_square]

theorem gamma0TrueWidthOppositeHeatFibre_eq (N : ℕ) [NeZero N] (r s : SL(2, ℤ))
    (c : Ioi (0 : ℕ)) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) (hmn : m*n < 0)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hp : tsupport f ⊆ Ioi (0 : ℝ)) (R : ℝ) (hR : 0 < R) :
    gamma0TrueWidthPhysicalFibre N r s c m n
      (spectralKLWeightedHeatProfile (spectralABLOppositeFourierWeight f) R) (spectralKLHeatProfile R) =
    gamma0TrueWidthHeatFibre N r s c m n (spectralABLOppositeFourierWeight f) R := by
  have hu := cuspFourierFrequency_ne_zero 1 zero_lt_one m hm
  have hv := cuspFourierFrequency_ne_zero 1 zero_lt_one n hn
  have hs := spectralWeyl_frequency_sign_sq hu
  have ht := spectralWeyl_frequency_sign_sq hv
  have he := spectralWeyl_frequency_sign_product hu hv
  have hpos := spectralWeyl_cusp_frequency_product_pos zero_lt_one m n
  have hnpos : ¬ 0 < m*n := not_lt_of_ge hmn.le
  rw [ite_eq_right (fun h => hnpos (hpos.mp h))] at he
  have hm0 := abs_pos.mpr hu
  have hn0 := abs_pos.mpr hv
  have hC := gamma0TrueWidthModulus_pos N r s (Nat.cast_pos.mpr c.property)
  unfold gamma0TrueWidthPhysicalFibre gamma0TrueWidthHeatFibre
  dsimp only
  rw [spectralWeylOppositeHeat_physical f hf hc hp (by positivity) R hR _ _ hs ht he]
  simp only [spectralABLHeatKernel,spectralWeylIntegerSignMultiplier,ite_eq_right hnpos]

/-- The actual Gaussian trace for the opposite-sign transform of a
compact test, in the same chart or in inequivalent cusp charts. -/
theorem gamma0HeatOpposite_source_trace (N : ℕ) [NeZero N] (r s : SL(2, ℤ))
    (hchart : r = s ∨ ¬ gamma0EisensteinCuspsEquivalent N r s)
    (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) (hmn : m*n < 0)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hp : tsupport f ⊆ Ioi (0 : ℝ)) (hr : ∀ x, star (f x) = f x) (R : ℝ) (hR : 0 < R) :
    gamma0HeatSourceSpectralSide N (spectralABLOppositeEnergyTest f hf hc hp) r s Y hY m n hm hn R =
      (1/4 : ℂ)*(∑' c : Ioi (0 : ℕ),
        gamma0TrueWidthHeatFibre N r s c m n (spectralABLOppositeFourierWeight f) R) := by
  let H := spectralABLOppositeFourierWeight f
  let G := spectralKLWeightedHeatProfile H R
  let h := spectralABLOppositeEnergyTest f hf hc hp
  let P := gamma0HeatHeightProfile N r m hm R hR
  obtain ⟨C,hC,hbound⟩ := spectralABLOppositeFourierWeight_strip_bound f hf hc hp
  have he := spectralABLOppositeFourierWeight_even f hp
  have hs := spectralABLOppositeFourierWeight_real_smooth f hf.continuous hc hp
  have hh (z : ℂ) (_hz : |z.im| ≤ 3/4) := spectralABLOppositeFourierWeight_entire f hf.continuous hc hp z
  have hG := spectralKLWeightedHeatProfile_properties H R hR he hs hh C hC hbound
  have hz := spectralKLWeightedHeatProfile_nonpositive_zero H R
  have hreal := spectralKLWeightedHeatProfile_real H R (fun t =>
    spectralABLOppositeFourierWeight_star_of_axis f hp hr (t : ℂ) (Or.inl (Complex.ofReal_im t)))
  obtain ⟨Q,hQ,_,hphysical,_,hact⟩ := gamma0HeatPoincareTest_window_action N s n hn R hR G hG hz hreal
    H h (spectralABLOppositeEnergyTest_real f hf hc hp hr)
    (fun l => (spectralABLOppositeEnergyTest_order f hf hc hp l).symm)
    (fun t => (spectralABLOppositeEnergyTest_continuous_symbol f hf hc hp t).symm)
    (spectralKLWeightedHeatProfile_continued_transform H R hR he hs hh C hC hbound)
  have hF := spectralKLHeatRegularity_five_eighths _ (spectralKLHeatProfile_properties R hR)
    (spectralKLHeatProfile_nonpositive_zero R)
  have hPphys : gamma0PrimitivePhysicalTest N r m P.value = spectralKLHeatProfile R :=
    gamma0HeatHeightProfile_physical N r m hm R hR
  have hMoment : Integrable
      (fun x : ℝ => x^(-(5/8 : ℝ))*‖gamma0PrimitivePhysicalTest N r m P.value x‖)
      spectralKLPhysicalMeasure := by simpa only [hPphys] using hF.1
  obtain ⟨M,hM,hpower⟩ := (spectralKLHeatRegularity_five_eighths G hG hz).2
  have hQpower : ∀ x, 0 < x → ‖gamma0PrimitivePhysicalTest N s n Q.value x‖ ≤ M*x^(5/8 : ℝ) := by
    simpa only [hphysical] using hpower
  have hgeom : inner ℂ (gamma0PrimitiveDecayingPoincare N r m P)
      (gamma0PrimitiveDecayingPoincare N s n Q) =
      ∑' c : Ioi (0 : ℕ), gamma0TrueWidthPhysicalFibre N r s c m n
        (gamma0PrimitivePhysicalTest N s n Q.value) (gamma0PrimitivePhysicalTest N r m P.value) := by
    rcases hchart with rfl | hneq
    · have hne : m ≠ n := by
        intro heq
        rw [heq] at hmn
        exact (not_lt_of_ge (mul_self_nonneg n)) hmn
      simpa only [ite_eq_right hne,zero_add] using
        gamma0TwoDecayingPoincare_sameCusp_physical N r m n hm hn P Q
          (by rw [hQ]; norm_num) (B := (5/8 : ℝ)) (by norm_num) (by norm_num) hM hMoment hQpower
    · exact gamma0TwoDecayingPoincare_inequivalent_physical N r s hneq m n hm hn P Q
        (by rw [hQ]; norm_num) (B := (5/8 : ℝ)) (by norm_num) (by norm_num) hM hMoment hQpower
  change gamma0HeatSourceSpectralSide N h r s Y hY m n hm hn R = _
  rw [← gamma0HeatPoincareTest_source_pairing_eq N h r s Y hY m n hm hn R hR,hact,inner_smul_right]
  change (1/4 : ℂ)*inner ℂ (gamma0PrimitiveDecayingPoincare N r m P)
    (gamma0PrimitiveDecayingPoincare N s n Q) = _
  rw [hgeom,hphysical,hPphys]
  congr 1
  exact tsum_congr (fun c => gamma0TrueWidthOppositeHeatFibre_eq N r s c m n hm hn hmn f hf hc hp R hR)

end
end ArtinMatthews
