module

public import ArtinMatthews.SourceComplexAdelicNorm
public import ArtinMatthews.SourceProductFourierDecay
public import OAI.RepresentationTheory.Weil.AdelicSplitting.RapidLatticePoisson


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.VaryingKummerAnalytic
open MeasureTheory
open scoped BigOperators Classical
noncomputable section
variable {ι : Type*} [Fintype ι]

def sourceComplexTraceForm : LinearMap.BilinForm ℝ (ι → ℂ) :=
  LinearMap.mk₂ ℝ (fun x y => ∑ i, 2 * (x i * y i).re)
    (by intro x y z; simp [add_mul, mul_add, Finset.sum_add_distrib])
    (by
      intro r x y
      simp only [Pi.smul_apply, Complex.real_smul, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero, smul_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring)
    (by intro x y z; simp [mul_add, Finset.sum_add_distrib])
    (by
      intro r x y
      simp only [Pi.smul_apply, Complex.real_smul, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero, smul_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring)

theorem sourceComplexTraceForm_apply (x y : ι → ℂ) :
    sourceComplexTraceForm x y = ∑ i, 2 * (x i * y i).re := rfl

theorem sourceComplexTraceForm_symmetric (x y : ι → ℂ) :
    sourceComplexTraceForm x y = sourceComplexTraceForm y x := by
  simp only [sourceComplexTraceForm_apply, mul_comm]

theorem sourceComplexTraceForm_separating :
    (sourceComplexTraceForm (ι := ι)).SeparatingLeft := by
  intro x hx
  funext i
  have hi := hx (Pi.single i (star (x i)))
  have heq : sourceComplexTraceForm x (Pi.single i (star (x i))) = 2 * ‖x i‖ ^ 2 := by
    rw [sourceComplexTraceForm_apply, Finset.sum_eq_single i]
    · simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      rw [← Complex.ofReal_pow, Complex.ofReal_re]
    · intro j _ hji
      simp [hji]
    · simp
  rw [heq] at hi
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg (x i)])

instance sourceComplexTraceMeasure_isAddHaar : sourceComplexTraceMeasure.IsAddHaarMeasure := by
  change ((2 : ENNReal) • (volume : Measure ℂ)).IsAddHaarMeasure
  exact Measure.IsAddHaarMeasure.smul volume (by norm_num : (2 : ENNReal) ≠ 0)
    (by norm_num : (2 : ENNReal) ≠ ⊤)

instance sourceComplexProductMeasure_isAddHaar :
    (sourceComplexProductMeasure ι).IsAddHaarMeasure := by
  unfold sourceComplexProductMeasure
  infer_instance

theorem sourceComplexProductFourier_eq_realBilinear (f : (ι → ℂ) → ℂ) (y : ι → ℂ) :
    sourceComplexProductFourier f y =
      OAI.RepresentationTheory.Weil.AdelicSplitting.LatticePoisson.LocalAnalysis.realBilinearFourier
        sourceComplexTraceForm (sourceComplexProductMeasure ι) f y := by
  unfold sourceComplexProductFourier
    OAI.RepresentationTheory.Weil.AdelicSplitting.LatticePoisson.LocalAnalysis.realBilinearFourier
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    dsimp only
    rw [sourceComplexTraceForm_symmetric, sourceComplexTraceForm_apply, Circle.smul_def]
    simp only [OAI.RepresentationTheory.Weil.AdelicSplitting.RealCharacters.LocalAnalysis.realCharacter_apply,
      Real.fourierChar_apply, mul_one, smul_eq_mul]
    push_cast
    ring

end
end ArtinMatthews.VaryingKummerAnalytic
