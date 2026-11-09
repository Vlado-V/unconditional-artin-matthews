module

public import ArtinMatthews.VaryingKummerAnalyticMixedPartialCompletion
public import ArtinMatthews.VaryingKummerAnalyticDedekindSeriesClasses


set_option backward.privateInPublic true
@[expose] public section

/-! An entire completed Dedekind zeta function for every number field, constructed
from its genuine mixed-signature ideal theta integrals. The identification on
Re(s)>1 is with the actual Mathlib Dedekind Dirichlet series. Every field-degree,
discriminant, roots-of-unity, and complex-place factor is explicit. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Set
open NumberField.Units
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

/-- The covolume of the ring of integers in the unweighted mixed Euclidean space. -/
def mixedDiscriminantScale : ℝ :=
  (2⁻¹ : ℝ) ^ InfinitePlace.nrComplexPlaces K * Real.sqrt |(discr K : ℝ)|

theorem mixedDiscriminantScale_pos : 0 < mixedDiscriminantScale K := by
  apply mul_pos (pow_pos (by norm_num) _)
  apply Real.sqrt_pos.mpr
  exact abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero K))

/-- The constant produced by the true unit-orbit cardinality and radial Jacobian. -/
def mixedXiNormalization : ℝ :=
  (Module.finrank ℚ K : ℝ)^2 / 4 * (torsionOrder K : ℝ) * mixedRadialJacobian K

theorem mixedXiNormalization_pos : 0 < mixedXiNormalization K := by
  unfold mixedXiNormalization
  exact mul_pos (mul_pos (div_pos (sq_pos_of_pos (Nat.cast_pos.mpr Module.finrank_pos))
    (by norm_num)) (Nat.cast_pos.mpr (torsionOrder_pos K))) (mixedRadialJacobian_pos K)

/-- The entire function obtained from the finite ideal-class sum of actual theta
continuations. The normalization is independent of the spectral variable. -/
def mixedCompletedDedekindXi (s : ℂ) : ℂ :=
  (mixedXiNormalization K : ℂ)⁻¹ * (mixedDiscriminantScale K : ℂ)^s *
    ∑ c : ClassGroup (𝓞 K),
      ((FractionalIdeal.absNorm (classRepresentative K c).1 : ℝ) : ℂ)^s *
        mixedIdealUnitXi K (classRepresentative K c) s

/-- Actual entire continuation in arbitrary signature. -/
theorem mixedCompletedDedekindXi_entire :
    Differentiable ℂ (mixedCompletedDedekindXi K) := by
  have hd : Differentiable ℂ (fun s : ℂ => (mixedDiscriminantScale K : ℂ)^s) :=
    Differentiable.const_cpow differentiable_id
      (Or.inl (Complex.ofReal_ne_zero.mpr (mixedDiscriminantScale_pos K).ne'))
  have hc : ∀ c : ClassGroup (𝓞 K), Differentiable ℂ (fun s : ℂ =>
      ((FractionalIdeal.absNorm (classRepresentative K c).1 : ℝ) : ℂ)^s *
        mixedIdealUnitXi K (classRepresentative K c) s) := by
    intro c
    exact (Differentiable.const_cpow differentiable_id
      (Or.inl (Complex.ofReal_ne_zero.mpr
        (fractionalIdeal_absNorm_pos (classRepresentative K c)).ne'))).mul
      (mixedIdealUnitXi_entire K _)
  unfold mixedCompletedDedekindXi
  fun_prop

/-- Canceling the actual representative norm gives the same completion factor
for every ideal class. -/
theorem mixedIdealUnitXi_normalized {s : ℂ} (hs : 1 < s.re)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ((FractionalIdeal.absNorm I.1 : ℝ) : ℂ)^s * mixedIdealUnitXi K I s =
      (mixedXiNormalization K : ℂ) * s * (s-1) * mixedGammaFactor K s *
        mixedPartialDedekindDirichlet K I s := by
  have h0 : ((FractionalIdeal.absNorm I.1 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (fractionalIdeal_absNorm_pos I).ne'
  have hc : ((FractionalIdeal.absNorm I.1 : ℝ) : ℂ)^s *
      ((FractionalIdeal.absNorm I.1 : ℝ) : ℂ)^(-s) = 1 := by
    rw [← Complex.cpow_add _ _ h0]
    simp
  rw [mixedIdealUnitXi_eq_partialCompletion K I hs]
  unfold mixedPartialThetaCompletion
  calc
    _ = (((Module.finrank ℚ K : ℂ)*s/2) *
          ((Module.finrank ℚ K : ℂ)*s/2 - (Module.finrank ℚ K : ℂ)/2) *
          (torsionOrder K : ℂ) * (mixedRadialJacobian K : ℂ) * mixedGammaFactor K s *
          mixedPartialDedekindDirichlet K I s) *
        (((FractionalIdeal.absNorm I.1 : ℝ) : ℂ)^s *
          ((FractionalIdeal.absNorm I.1 : ℝ) : ℂ)^(-s)) := by ring
    _ = _ := by
      rw [hc]
      simp only [mixedXiNormalization, Complex.ofReal_mul, Complex.ofReal_div,
        Complex.ofReal_pow, Complex.ofReal_natCast, Complex.ofReal_ofNat]
      ring

/-- This constructed entire function is exactly the Gamma-completed actual
Dedekind zeta function throughout the half-plane of absolute convergence. -/
theorem mixedCompletedDedekindXi_eq {s : ℂ} (hs : 1 < s.re) :
    mixedCompletedDedekindXi K s =
      s * (s-1) * (mixedDiscriminantScale K : ℂ)^s * mixedGammaFactor K s *
        NumberField.dedekindZeta K s := by
  unfold mixedCompletedDedekindXi
  simp_rw [mixedIdealUnitXi_normalized K hs]
  rw [← Finset.mul_sum, ← dedekindZeta_eq_partial_class_sum K hs]
  have h0 : (mixedXiNormalization K : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (mixedXiNormalization_pos K).ne'
  field_simp

end
end ArtinMatthews.VaryingKummerAnalytic
