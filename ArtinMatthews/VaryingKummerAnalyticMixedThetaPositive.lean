module

public import ArtinMatthews.VaryingKummerAnalyticMixedGaussianNorm


set_option backward.privateInPublic true
@[expose] public section

/-! Identification of the real part of the actual complex theta function with
its positive nonzero Gaussian series. The three generic lattice-energy lemmas
are exact extracts from OpenAI PrimePackets/LatticeTheta.lean. -/
namespace ArtinMatthews.ReusedTheta
open scoped Classical BigOperators
noncomputable section
variable {d : Type*} [Fintype d]
def latticeEnergy (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (z : NonzeroIntegerVector d) : ℝ := Real.pi * ‖B (euclideanInteger z.1)‖^2

lemma latticeEnergy_pos (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (z : NonzeroIntegerVector d) : 0 < latticeEnergy B z := by
  obtain ⟨c,hc,hbound⟩ := theta_lattice_lower_bound B
  exact mul_pos Real.pi_pos (sq_pos_of_pos (hc.trans_le (hbound z)))

lemma thetaRemainder_eq_real_sum (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    {t : ℝ} (_ht : 0 < t) : thetaRemainder B (Real.pi*t) =
      ((∑' z : NonzeroIntegerVector d, Real.exp (-latticeEnergy B z*t)):ℝ) := by
  unfold thetaRemainder
  rw [Complex.ofReal_tsum]
  congr 1
  funext z
  rw [Complex.ofReal_exp]
  congr 1
  simp only [latticeEnergy,Complex.ofReal_mul,Complex.ofReal_neg,Complex.ofReal_pow]
  ring

lemma realGaussian_summable (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    {t : ℝ} (ht : 0 < t) :
    Summable (fun z : NonzeroIntegerVector d => Real.exp (-latticeEnergy B z*t)) := by
  have H := (thetaRemainder_summable B (mul_pos Real.pi_pos ht)).norm
  convert H using 1
  funext z
  rw [gaussianTerm_norm]
  congr 1
  simp only [latticeEnergy]
  ring

 


end
end ArtinMatthews.ReusedTheta

namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField NumberField.mixedEmbedding MeasureTheory
open NumberField.Units NumberField.Units.dirichletUnitTheorem
open ArtinMatthews.ReusedTheta
open scoped NumberField nonZeroDivisors Classical BigOperators ENNReal
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

def mixedIdealNonzeroIntegerEquiv :
    NonzeroIntegerVector (MixedIdealIndex K I) ≃ nonzeroIdealElements I := by
  let e : NonzeroIntegerVector (MixedIdealIndex K I) ≃ {a : I.1 // (a : K) ≠ 0} :=
    (fractionalIdealBasis K I.1).equivFun.symm.toEquiv.subtypeEquiv (by
      intro z
      constructor
      · intro hz h
        apply hz
        apply (fractionalIdealBasis K I.1).equivFun.symm.injective
        rw [map_zero]
        exact Subtype.ext h
      · intro hz h
        apply hz
        change ((fractionalIdealBasis K I.1).equivFun.symm z : K) = 0
        rw [h, map_zero]
        rfl)
  exact e.trans (nonzeroIdealElementEquiv I)

theorem mixedIdealFlowTheta_real_nonzero (u : logSpace K) {t : ℝ} (ht : 0 < t) :
    ENNReal.ofReal ((mixedIdealFlowTheta K I u t - 1).re) =
      mixedIdealPositiveThetaTail K I u t := by
  rw [mixedIdealFlowTheta_eq_normalizedTheta, mixedIdealPositiveThetaTail_eq]
  let B := logScaledLattice (mixedIdealMatrix K I) (mixedIdealLogScale K I u)
  let e := mixedIdealNonzeroIntegerEquiv K I
  have he (z : NonzeroIntegerVector (MixedIdealIndex K I)) :
      mixedArchGaussian K (e z).1.1 t u =
        ENNReal.ofReal (Real.exp (-latticeEnergy B z*t)) := by
    change mixedArchGaussian K ((fractionalIdealBasis K I.1).equivFun.symm z.1 : K) t u = _
    unfold mixedArchGaussian latticeEnergy
    have hv : B (euclideanInteger z.1) =
        logScale (mixedIdealLogScale K I u) ((mixedIdealOrthonormalBasis K I).repr
          (mixedIdealEmbedding K I ((fractionalIdealBasis K I.1).equivFun.symm z.1))) := by
      change logScale _ ((mixedIdealOrthonormalBasis K I).repr
        ((mixedIdealEuclideanBasis K I).equivFun.symm (fun j => (z.1 j : ℝ)))) = _
      rw [mixedIdealEuclideanBasis_integer_apply]
    rw [hv, mixedIdealFlow_norm_sq]
    congr 2
    ring
  change ENNReal.ofReal ((normalizedTheta B t-1).re) = _
  rw [normalizedTheta, ← thetaRemainder_eq B (mul_pos Real.pi_pos ht),
    thetaRemainder_eq_real_sum B ht, Complex.ofReal_re,
    ENNReal.ofReal_tsum_of_nonneg (fun z => (Real.exp_pos _).le) (realGaussian_summable B ht)]
  calc
    _ = ∑' z, mixedArchGaussian K (e z).1.1 t u := tsum_congr (fun z => (he z).symm)
    _ = _ := e.tsum_eq (fun a => mixedArchGaussian K a.1.1 t u)

end
end ArtinMatthews.VaryingKummerAnalytic
