module

public import ArtinMatthews.VaryingKummerAnalyticMixedPrimitiveThetaCosets


set_option backward.privateInPublic true
@[expose] public section

/-! Absolute convergence of the literal primal and dual weighted ideal theta
sums. These statements do not require a primitive or nontrivial character. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open Module NumberField FractionalIdeal
open NumberField.Units NumberField.Units.dirichletUnitTheorem
open ArtinMatthews.ReusedTheta
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
set_option maxHeartbeats 800000
variable (K : Type*) [Field K] [NumberField K]
variable (I M : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hM : M ≠ ⊥) [NeZero M]

theorem mixedPrimitiveTheta_summable (χ : MulChar ((𝓞 K) ⧸ M) ℂ)
    (u : logSpace K) {t : ℝ} (ht : 0 < t) :
    Summable (fun a : I => χ (idealResidueCoordinate I M hI hM a) *
      mixedComplexArchGaussian K ((a : 𝓞 K) : K) t u) := by
  apply (mixedPrimitiveCosetEquiv K I M hI hM).symm.summable_iff.mp
  have H (p : ((𝓞 K) ⧸ M) × (MixedConductorIndex K I M hI hM → ℤ)) :
      idealResidueCoordinate I M hI hM ((mixedPrimitiveCosetEquiv K I M hI hM).symm p) = p.1 :=
    congrArg Prod.fst ((mixedPrimitiveCosetEquiv K I M hI hM).apply_symm_apply p)
  simp only [Function.comp_def]
  simp_rw [H, mixedPrimitiveCosetEquiv_symm_coe, ← mixedIdealCosetPoint_gaussian]
  exact mixedPrimitiveCosetProduct_summable K I M hI hM χ u ht

omit [NeZero M] in
/-- The trace-dual weighted theta is absolutely convergent at every positive
scale, including the conductor-one case. -/
theorem mixedPrimitiveDualTheta_summable (χ : MulChar ((𝓞 K) ⧸ M) ℂ)
    (u : logSpace K) {t : ℝ} (ht : 0 < t) :
    Summable (fun β : (mixedTraceDualIdeal K (mixedConductorIdeal K I M hI hM)).val =>
      χ⁻¹ (idealModuleDualResidue K I M hI hM β β.property) *
        Complex.exp (-((Real.pi * t : ℝ) : ℂ) *
          ((∑ w : InfinitePlace K,
            ((w.mult : ℝ) * mixedPlaceWeight K u w * w (β : K))^2 : ℝ) : ℂ))) := by
  let : Finite ((𝓞 K) ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient hM
  apply (mixedDualIntegerEquiv K (mixedConductorIdeal K I M hI hM)).summable_iff.mp
  have H := latticeTheta_summable
    (logScaledLattice (adjointEquiv (mixedIdealMatrix K (mixedConductorIdeal K I M hI hM)).symm)
      (mixedIdealLogScale K (mixedConductorIdeal K I M hI hM) u))
    (Real.pi*t) (mul_pos Real.pi_pos ht)
  change Summable (fun z : MixedConductorIndex K I M hI hM → ℤ =>
    Complex.exp (-((Real.pi*t : ℝ) : ℂ) *
      ‖logScale (mixedIdealLogScale K (mixedConductorIdeal K I M hI hM) u)
        (adjointEquiv (mixedIdealMatrix K (mixedConductorIdeal K I M hI hM)).symm
          (euclideanInteger z))‖^2)) at H
  simp_rw [mixedDualIntegerEquiv_coordinates, ← Complex.ofReal_pow,
    mixedTraceDualFlow_norm_sq] at H
  apply Summable.of_norm_bounded H.norm
  intro z
  simp only [Function.comp_def, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (finiteMulChar_norm_le_one _ _)

end
end ArtinMatthews.VaryingKummerAnalytic
