module

public import ArtinMatthews.SpectralPeterssonFourierRows


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews

open Set MeasureTheory UpperHalfPlane
noncomputable section

private theorem spectralWeightTwo_height_continuous (y : ℝ) (hy : 0 < y) :
    Continuous (fun x : ℝ => spectralPeterssonHeightPoint x y hy) := by
  apply UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr
  simp only [Function.comp_def, spectralPeterssonHeightPoint_coe]
  fun_prop

theorem spectralWeightTwoFourier_integrable (F : UpperHalfPlane → ℂ)
    (hF : Continuous F) (n : ℕ+) (y : ℝ) (hy : 0 < y) :
    IntegrableOn (fun x => F (spectralPeterssonHeightPoint x y hy) *
      spectralPeterssonFourierWeight n (spectralPeterssonHeightPoint x y hy)) (Ioc (0 : ℝ) 1) := by
  have hC : Continuous (fun x => F (spectralPeterssonHeightPoint x y hy) *
      spectralPeterssonFourierWeight n (spectralPeterssonHeightPoint x y hy)) := by
    apply (hF.comp (spectralWeightTwo_height_continuous y hy)).mul
    unfold spectralPeterssonFourierWeight
    simp_rw [spectralPeterssonHeightPoint_coe]
    fun_prop
  exact (hC.integrableOn_Icc (μ := volume) (a := 0) (b := 1)).mono_set Ioc_subset_Icc_self

theorem spectralWeightTwoFourier_add (F G : UpperHalfPlane → ℂ)
    (hF : Continuous F) (hG : Continuous G) (n : ℕ+) (y : ℝ) (hy : 0 < y) :
    spectralPeterssonFourierAtHeight (fun z => F z + G z) n y hy =
      spectralPeterssonFourierAtHeight F n y hy + spectralPeterssonFourierAtHeight G n y hy := by
  unfold spectralPeterssonFourierAtHeight
  simp only [add_mul]
  exact integral_add (spectralWeightTwoFourier_integrable F hF n y hy)
    (spectralWeightTwoFourier_integrable G hG n y hy)

theorem spectralWeightTwoFourier_sum {ι : Type*} [Fintype ι] (F : ι → UpperHalfPlane → ℂ)
    (hF : ∀ i, Continuous (F i)) (n : ℕ+) (y : ℝ) (hy : 0 < y) :
    spectralPeterssonFourierAtHeight (fun z => ∑ i, F i z) n y hy =
      ∑ i, spectralPeterssonFourierAtHeight (F i) n y hy := by
  classical
  unfold spectralPeterssonFourierAtHeight
  simp only [Finset.sum_mul]
  exact integral_finsetSum _ (fun i _ => spectralWeightTwoFourier_integrable (F i) (hF i) n y hy)

end
end ArtinMatthews
