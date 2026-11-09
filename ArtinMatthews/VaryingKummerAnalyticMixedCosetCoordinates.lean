module

public import ArtinMatthews.VaryingKummerAnalyticMixedTraceDualFlow
public import ArtinMatthews.VaryingKummerAnalyticMixedResidueGaussian
public import ArtinMatthews.VaryingKummerAnalyticCosetTheta


set_option backward.privateInPublic true
@[expose] public section

/-! Coordinates for arbitrary field translates of an actual mixed ideal lattice.
The Fourier phase is the literal field trace, including the complex-place factors. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open Module NumberField NumberField.mixedEmbedding
open NumberField.Units NumberField.Units.dirichletUnitTheorem
open ArtinMatthews.ReusedTheta
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

def mixedIdealCosetPoint (a : K) : MixedIdealIndex K I → ℝ :=
  (mixedIdealMatrix K I).symm
    ((mixedIdealOrthonormalBasis K I).repr (mixedFieldEmbedding K a))

theorem mixedIdealCosetPoint_trace (a : K) (z : MixedIdealIndex K I → ℤ) :
    (Algebra.trace ℚ K (a * (mixedDualIntegerEquiv K I z : K)) : ℝ) =
      ∑ i, mixedIdealCosetPoint K I a i * (z i : ℝ) := by
  rw [← mixedTraceTransform_inner_eq_trace,
    ← (mixedIdealOrthonormalBasis K I).repr.inner_map_map,
    ← mixedDualIntegerEquiv_coordinates]
  change inner ℝ ((mixedIdealOrthonormalBasis K I).repr (mixedFieldEmbedding K a))
    ((mixedIdealMatrix K I).symm.toContinuousLinearMap.adjoint (euclideanInteger z)) = _
  rw [ContinuousLinearMap.adjoint_inner_right]
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  change (z i : ℝ) * mixedIdealCosetPoint K I a i = _
  ring

theorem mixedIdealCosetPoint_fourier (a : K) (z : MixedIdealIndex K I → ℤ) :
    UnitAddTorus.mFourier z (torusProjection (mixedIdealCosetPoint K I a)) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
        ((Algebra.trace ℚ K (a * (mixedDualIntegerEquiv K I z : K)) : ℚ) : ℂ)) := by
  have ht := congrArg (fun x : ℝ => (x : ℂ)) (mixedIdealCosetPoint_trace K I a z)
  push_cast at ht
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, torusProjection,
    fourier_coe_apply, Complex.ofReal_one, div_one]
  rw [← Complex.exp_sum]
  congr 1
  rw [ht, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem mixedFieldFlow_norm_sq (a : K) (u : logSpace K) :
    ‖logScale (mixedIdealLogScale K I u)
      ((mixedIdealOrthonormalBasis K I).repr (mixedFieldEmbedding K a))‖^2 =
      mixedArchEnergy K a u := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp_rw [logScale_apply]
  change (∑ j, (Real.exp (mixedStandardLogScale K u (mixedIdealIndexEquiv K I j)) *
    (mixedEmbedding.stdBasis K).repr (mixedEmbedding K a)
      (mixedIdealIndexEquiv K I j))^2) = _
  rw [(mixedIdealIndexEquiv K I).sum_comp (fun j =>
    (Real.exp (mixedStandardLogScale K u j) *
      (mixedEmbedding.stdBasis K).repr (mixedEmbedding K a) j)^2),
    Fintype.sum_sum_type]
  unfold mixedArchEnergy
  rw [InfinitePlace.sum_eq_sum_add_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro w _
    simp only [mixedStandardLogScale, mixedPlaceWeight,
      InfinitePlace.mult_isReal w, Nat.cast_one, div_one,
      mixedEmbedding.stdBasis_apply_isReal]
    change (Real.exp _ * InfinitePlace.embedding_of_isReal w.property a)^2 = _
    rw [mul_pow, mul_pow, ← InfinitePlace.norm_embedding_of_isReal w.property,
      Real.norm_eq_abs, sq_abs]
  · rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro w _
    simp only [Fin.sum_univ_two, mixedStandardLogScale,
      mixedEmbedding.stdBasis_apply_isComplex_fst,
      mixedEmbedding.stdBasis_apply_isComplex_snd,
      mixedPlaceWeight, InfinitePlace.mult_isComplex w, Nat.cast_ofNat]
    change (Real.exp _ * (w.1.embedding a).re)^2 +
      (Real.exp _ * (w.1.embedding a).im)^2 = _
    rw [← InfinitePlace.norm_embedding_eq]
    simp only [mul_pow, Complex.sq_norm, Complex.normSq_apply]
    ring

theorem mixedIdealCosetPoint_shift (a : K) (z : MixedIdealIndex K I → ℤ) :
    mixedIdealMatrix K I (WithLp.toLp 2 (mixedIdealCosetPoint K I a) + euclideanInteger z) =
      (mixedIdealOrthonormalBasis K I).repr (mixedFieldEmbedding K
        (a + ((fractionalIdealBasis K I.val).equivFun.symm z : I.val))) := by
  rw [map_add]
  change mixedIdealMatrix K I ((mixedIdealMatrix K I).symm
    ((mixedIdealOrthonormalBasis K I).repr (mixedFieldEmbedding K a))) +
      (mixedIdealOrthonormalBasis K I).repr
        ((mixedIdealEuclideanBasis K I).equivFun.symm (fun j => (z j : ℝ))) = _
  rw [ContinuousLinearEquiv.apply_symm_apply, mixedIdealEuclideanBasis_integer_apply]
  simp only [mixedFieldEmbedding, mixedIdealEmbedding, map_add]

theorem mixedIdealCosetPoint_gaussian (a : K) (z : MixedIdealIndex K I → ℤ)
    (u : logSpace K) (t : ℝ) :
    Complex.exp (-((Real.pi*t : ℝ) : ℂ) *
      ‖logScaledLattice (mixedIdealMatrix K I) (mixedIdealLogScale K I u)
        (WithLp.toLp 2 (mixedIdealCosetPoint K I a) + euclideanInteger z)‖^2) =
      mixedComplexArchGaussian K
        (a + ((fractionalIdealBasis K I.val).equivFun.symm z : I.val)) t u := by
  change Complex.exp (-((Real.pi*t : ℝ) : ℂ) *
    ‖logScale (mixedIdealLogScale K I u) (mixedIdealMatrix K I _)‖^2) = _
  rw [mixedIdealCosetPoint_shift, ← Complex.ofReal_pow, mixedFieldFlow_norm_sq]
  unfold mixedComplexArchGaussian
  congr 1
  push_cast
  ring

end
end ArtinMatthews.VaryingKummerAnalytic
