module

public import ArtinMatthews.VaryingKummerAnalyticMixedTraceDual
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.Norm
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar


set_option backward.privateInPublic true
@[expose] public section

/-! The actual archimedean trace and its standard unitary exponential.
Complex places contribute twice the real part, so rational elements give
the genuine field trace. -/
namespace ArtinMatthews.StandardAdelic

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open NumberField.InfinitePlace.Completion
open scoped NumberField BigOperators Classical
noncomputable section
variable (K : Type) [Field K] [NumberField K]

def mixedTrace (x : mixedSpace K) : ℝ :=
  (∑ v : {v : InfinitePlace K // IsReal v}, x.1 v) +
    ∑ v : {v : InfinitePlace K // IsComplex v}, 2 * (x.2 v).re

def archTrace : InfiniteAdeleRing K →+ ℝ where
  toFun x := mixedTrace K (InfiniteAdeleRing.ringEquiv_mixedSpace K x)
  map_zero' := by
    change mixedTrace K (InfiniteAdeleRing.ringEquiv_mixedSpace K 0) = 0
    rw [map_zero]
    simp [mixedTrace]
  map_add' x y := by
    simp only [map_add, mixedTrace, Prod.fst_add, Prod.snd_add, Pi.add_apply,
      Complex.add_re, mul_add, Finset.sum_add_distrib]
    ring

theorem archTrace_continuous : Continuous (archTrace K) := by
  have hr (v : {v : InfinitePlace K // IsReal v}) :
      Continuous (fun x : InfiniteAdeleRing K => extensionEmbeddingOfIsReal v.property (x v)) :=
    (isometry_extensionEmbeddingOfIsReal v.property).continuous.comp (continuous_apply v.val)
  have hc (v : {v : InfinitePlace K // IsComplex v}) :
      Continuous (fun x : InfiniteAdeleRing K => (extensionEmbedding v.val (x v)).re) :=
    Complex.continuous_re.comp ((isometry_extensionEmbedding v.val).continuous.comp (continuous_apply v.val))
  change Continuous (fun x : InfiniteAdeleRing K =>
    (∑ v : {v : InfinitePlace K // IsReal v}, extensionEmbeddingOfIsReal v.property (x v)) +
      ∑ v : {v : InfinitePlace K // IsComplex v}, 2 * (extensionEmbedding v.val (x v)).re)
  fun_prop

theorem archTrace_rational (q : K) :
    archTrace K (algebraMap K (InfiniteAdeleRing K) q) = (Algebra.trace ℚ K q : ℝ) := by
  change mixedTrace K (InfiniteAdeleRing.ringEquiv_mixedSpace K (algebraMap K (InfiniteAdeleRing K) q)) = _
  rw [← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
  exact (VaryingKummerAnalytic.trace_eq_mixed_sum K q).symm

def archCharacter : AddChar (InfiniteAdeleRing K) ℂ where
  toFun x := Complex.exp ((archTrace K x : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))
  map_zero_eq_one' := by simp
  map_add_eq_mul' x y := by
    rw [map_add, Complex.ofReal_add, add_mul, Complex.exp_add]

theorem archCharacter_continuous : Continuous (archCharacter K) :=
  Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp (archTrace_continuous K)).mul continuous_const)

theorem archCharacter_unitary (x : InfiniteAdeleRing K) : ‖archCharacter K x‖ = 1 := by
  simp [archCharacter, Complex.norm_exp, Complex.mul_re]

theorem archCharacter_rational (q : K) :
    archCharacter K (algebraMap K (InfiniteAdeleRing K) q) =
      Complex.exp ((Algebra.trace ℚ K q : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) := by
  change Complex.exp ((archTrace K _ : ℂ) * _) = _
  rw [archTrace_rational]
  norm_cast

theorem archCharacter_integer (r : 𝓞 K) :
    archCharacter K (algebraMap K (InfiniteAdeleRing K) (r : K)) = 1 := by
  rw [archCharacter_rational]
  have htrace := Algebra.coe_trace_int (K := K) r
  rw [← htrace]
  exact Complex.exp_int_mul_two_pi_mul_I (Algebra.trace ℤ (𝓞 K) r)

end
end ArtinMatthews.StandardAdelic
