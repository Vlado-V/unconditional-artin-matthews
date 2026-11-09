module

public import ArtinMatthews.VaryingKummerAnalyticMixedCovolume


set_option backward.privateInPublic true
@[expose] public section

/-! Exact discriminant normalization of the mixed-signature Gaussian matrix. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open Module NumberField NumberField.mixedEmbedding MeasureTheory ZSpan
open scoped NumberField nonZeroDivisors Classical

noncomputable section

variable (K : Type*) [Field K] [NumberField K]
variable (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

/-- The absolute Gaussian determinant is the covolume of the actual ideal lattice. -/
theorem mixedIdealMatrix_abs_det_eq_covolume :
    |LinearMap.det (mixedIdealMatrix K I).toLinearMap| =
      ZLattice.covolume (mixedIdealLattice K I) := by
  let b := mixedIdealOrthonormalBasis K I
  have hvol : volume.real (fundamentalDomain b.toBasis) = 1 := by
    rw [measureReal_congr (fundamentalDomain_ae_parallelepiped b.toBasis volume),
      measureReal_def]
    exact congrArg ENNReal.toReal b.volume_parallelepiped
  have hc := ZLattice.covolume_eq_det_mul_measureReal (mixedIdealLattice K I)
    volume (mixedIdealIntegralBasis K I) b.toBasis
  rw [hvol, mul_one] at hc
  rw [mixedIdealMatrix_det]
  convert hc.symm using 1
  congr 2
  funext j
  exact (mixedIdealIntegralBasis_apply K I j).symm

/-- All discriminant and complex-place factors in Poisson inversion are exact. -/
theorem mixedIdealMatrix_abs_det :
    |LinearMap.det (mixedIdealMatrix K I).toLinearMap| =
      (FractionalIdeal.absNorm I.1 : ℝ) *
        (2⁻¹ : ℝ) ^ InfinitePlace.nrComplexPlaces K * Real.sqrt |(discr K : ℝ)| := by
  rw [mixedIdealMatrix_abs_det_eq_covolume, mixedIdealLattice_covolume]

end
end ArtinMatthews.VaryingKummerAnalytic
