module

public import ArtinMatthews.VaryingKummerAnalyticMixedResidueGaussian


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine nonzero-element and unit-orbit reindexing of mixed residue theta.
The ideal-element equivalence and absolutely convergent reindexing are adapted
from OpenAI PrimePackets/UnitOrbitIntegrals; all Gaussian norms are the actual
mixed-signature Gaussian proved here. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Module MeasureTheory Set Filter
open NumberField.Units NumberField.Units.dirichletUnitTheorem
open ArtinMatthews.ReusedTheta
open scoped NumberField nonZeroDivisors Classical BigOperators ENNReal
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
lemma mixedComplexArchGaussian_ideal_summable_norm
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (u : logSpace K)
    {t : ℝ} (ht : 0 < t) :
    Summable (fun a : nonzeroIdealElements I => ‖mixedComplexArchGaussian K a.1.1 t u‖) := by
  apply tsum_enorm_ne_top_iff_summable_norm.mp
  simp_rw [mixedComplexArchGaussian_enorm]
  rw [← mixedIdealPositiveThetaTail_eq K I u t, ← mixedIdealFlowTheta_real_nonzero K I u ht]
  exact ENNReal.ofReal_ne_top

lemma mixedResidueWeightedGaussian_summable
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (N : ℕ) [NeZero N]
    (χ : MulChar ((𝓞 K) ⧸ rationalModulusIdeal (𝓞 K) N) ℂ)
    (u : logSpace K) {t : ℝ} (ht : 0 < t) :
    Summable (fun a : nonzeroIdealElements (integralIdealFractionalUnit I hI) =>
      idealResidueElementWeight I hI N χ a * mixedComplexArchGaussian K a.1.1 t u) := by
  apply (mixedComplexArchGaussian_ideal_summable_norm K
    (integralIdealFractionalUnit I hI) u ht).of_norm_bounded
  intro a
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _)
    (idealResidueElementWeight_norm_le_one I hI N χ a)

 

theorem mixedResidueWeightedGaussian_ideal_units
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (N : ℕ) [NeZero N]
    (χ : MulChar ((𝓞 K) ⧸ rationalModulusIdeal (𝓞 K) N) ℂ)
    (hunit : ∀ z : (𝓞 K)ˣ,
      χ (Ideal.Quotient.mk (rationalModulusIdeal (𝓞 K) N) (z:𝓞 K)) = 1)
    (u : logSpace K) {t : ℝ} (ht : 0 < t) :
    (∑' a : nonzeroIdealElements (integralIdealFractionalUnit I hI),
      idealResidueElementWeight I hI N χ a * mixedComplexArchGaussian K a.1.1 t u) =
    ∑' J : integralIdealClassFiber (integralIdealFractionalUnit I hI),
      idealResidueCoefficient I hI N χ J *
        ∑' z : (𝓞 K)ˣ, mixedComplexArchGaussian K
          ((z:K)*(idealElementRepresentative _ J).1.1) t u := by
  let F := fun a : nonzeroIdealElements (integralIdealFractionalUnit I hI) =>
    idealResidueElementWeight I hI N χ a * mixedComplexArchGaussian K a.1.1 t u
  let e := idealElementDecomposition (integralIdealFractionalUnit I hI)
  have HS : Summable (fun x => F (e x)) := e.summable_iff.mpr
    (mixedResidueWeightedGaussian_summable K I hI N χ u ht)
  rw [← e.tsum_eq F, HS.tsum_sigma]
  apply tsum_congr
  intro J
  rw [← tsum_mul_left]
  apply tsum_congr
  intro z
  change idealResidueElementWeight I hI N χ
    (idealElementUnitAction _ z (idealElementRepresentative _ J)) * _ = _
  rw [idealResidueElementWeight_unitAction,hunit,one_mul]
  rfl

 
def integralIdealNonzeroEquiv (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    {a : I // a ≠ 0} ≃ nonzeroIdealElements (integralIdealFractionalUnit I hI) where
  toFun a := ⟨Units.mk0 (((a.1:I):𝓞 K):K) (by
    intro h
    apply a.2
    apply Subtype.ext
    exact NumberField.RingOfIntegers.coe_injective (by simpa using h)),
    FractionalIdeal.mem_coeIdeal_of_mem (𝓞 K)⁰ a.1.property⟩
  invFun a := ⟨⟨idealIntegerElement I hI a,
    ((FractionalIdeal.mem_coeIdeal (𝓞 K)⁰).mp a.property).choose_spec.1⟩, by
    intro h
    have H := congrArg (fun x : I => ((x:𝓞 K):K)) h
    simp only [ZeroMemClass.coe_zero,_root_.map_zero,idealIntegerElement_coe] at H
    exact a.1.ne_zero H⟩
  left_inv a := by
    apply Subtype.ext
    apply Subtype.ext
    apply NumberField.RingOfIntegers.coe_injective
    exact idealIntegerElement_coe I hI _
  right_inv a := by
    apply Subtype.ext
    apply Units.ext
    exact idealIntegerElement_coe I hI a

lemma mixedIdealResidueFlowTheta_nonzero
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (N : ℕ)
    (χ : MulChar ((𝓞 K) ⧸ rationalModulusIdeal (𝓞 K) N) ℂ) (hχ : χ ≠ 1)
    (u : logSpace K) (t : ℝ) :
    mixedIdealResidueFlowTheta K I hI N χ u t =
    ∑' a : nonzeroIdealElements (integralIdealFractionalUnit I hI),
      idealResidueElementWeight I hI N χ a * mixedComplexArchGaussian K a.1.1 t u := by
  let : Nontrivial ((𝓞 K) ⧸ rationalModulusIdeal (𝓞 K) N) :=
    mulChar_nontrivial_domain χ hχ
  rw [mixedIdealResidueFlowTheta_eq_complex]
  let F := fun a : I =>
    χ (Ideal.Quotient.mk (rationalModulusIdeal (𝓞 K) N) (a:𝓞 K)) *
      mixedComplexArchGaussian K ((a:𝓞 K):K) t u
  change (∑' a, F a) = _
  have H : Function.support F ⊆ {a : I | a ≠ 0} := by
    intro a ha he
    subst a
    simp [F,Function.mem_support,MulChar.map_zero] at ha
  rw [← tsum_subtype_eq_of_support_subset H,
    ← (integralIdealNonzeroEquiv K I hI).tsum_eq]
  apply tsum_congr
  intro a
  have HA : idealIntegerElement I hI ((integralIdealNonzeroEquiv K I hI) a) =
      (a.1:𝓞 K) := NumberField.RingOfIntegers.coe_injective
        (idealIntegerElement_coe I hI _)
  simp only [F,idealResidueElementWeight,HA]
  rfl

 

theorem mixedIdealResidueFlowTheta_ideal_units
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (N : ℕ) [NeZero N]
    (χ : MulChar ((𝓞 K) ⧸ rationalModulusIdeal (𝓞 K) N) ℂ) (hχ : χ ≠ 1)
    (hunit : ∀ z : (𝓞 K)ˣ,
      χ (Ideal.Quotient.mk (rationalModulusIdeal (𝓞 K) N) (z:𝓞 K)) = 1)
    (u : logSpace K) {t : ℝ} (ht : 0 < t) :
    mixedIdealResidueFlowTheta K I hI N χ u t =
    ∑' J : integralIdealClassFiber (integralIdealFractionalUnit I hI),
      idealResidueCoefficient I hI N χ J *
        ∑' z : (𝓞 K)ˣ, mixedComplexArchGaussian K
          ((z:K)*(idealElementRepresentative _ J).1.1) t u := by
  rw [mixedIdealResidueFlowTheta_nonzero K I hI N χ hχ]
  exact mixedResidueWeightedGaussian_ideal_units K I hI N χ hunit u ht


end
end ArtinMatthews.VaryingKummerAnalytic
