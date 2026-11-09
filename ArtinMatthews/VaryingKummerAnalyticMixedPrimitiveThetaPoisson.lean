module

public import ArtinMatthews.VaryingKummerAnalyticMixedPrimitiveThetaCosets


set_option backward.privateInPublic true
@[expose] public section

/-! Primitive ideal-residue weighted Poisson summation on the actual mixed
ideal lattice. All trace-dual ideals, covolumes, and finite Gauss factors are
retained. This is a theta transform, not yet a Hecke functional equation. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open Module NumberField FractionalIdeal
open NumberField.Units NumberField.Units.dirichletUnitTheorem
open ArtinMatthews.ReusedTheta
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
set_option maxHeartbeats 800000
variable (K : Type*) [Field K] [NumberField K]
variable (I M : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hM : M ≠ ⊥) [NeZero M]

/-- Actual weighted theta inversion for arbitrary conductor M and arbitrary I,
including I sharing prime factors with M and nonprincipal trace-dual ideals. -/
theorem mixedPrimitiveTheta_poisson
    (χ : MulChar ((𝓞 K) ⧸ M) ℂ)
    (hχ : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals χ)
    (u : logSpace K) {t : ℝ} (ht : 0 < t) :
    mixedPrimitiveTheta K I M hI hM χ u t =
      (((((FractionalIdeal.absNorm (mixedConductorIdeal K I M hI hM).val : ℝ) *
        (2⁻¹ : ℝ) ^ InfinitePlace.nrComplexPlaces K * Real.sqrt |(discr K : ℝ)|)⁻¹) : ℝ) : ℂ) *
      (t : ℂ)^(-(((Module.finrank ℚ K : ℕ) : ℂ)/2)) *
      ∑' β : (mixedTraceDualIdeal K (mixedConductorIdeal K I M hI hM)).val,
        Complex.exp (-((Real.pi * t⁻¹ : ℝ) : ℂ) *
          ((∑ w : InfinitePlace K,
            ((w.mult : ℝ) * mixedPlaceWeight K (-u) w * w (β : K))^2 : ℝ) : ℂ)) *
        (χ⁻¹ (idealModuleDualResidue K I M hI hM β β.property) *
          idealTraceGaussSum K M χ) := by
  let : Finite ((𝓞 K) ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient hM
  let : Fintype ((𝓞 K) ⧸ M) := Fintype.ofFinite _
  rw [mixedPrimitiveTheta_eq_cosets K I M hI hM χ u ht,
    congruenceTheta_poisson _ _ _ _ (mul_pos Real.pi_pos ht)]
  have hπ : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have ht' : (t:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have h1 : (Real.pi:ℂ) / ((Real.pi*t:ℝ):ℂ) = (t:ℂ)⁻¹ := by
    rw [Complex.ofReal_mul]; field_simp
  have h2 : Real.pi^2/(Real.pi*t) = Real.pi*t⁻¹ := by field_simp
  rw [h1, h2, Complex.inv_cpow_ofReal_nonneg ht.le, ← Complex.cpow_neg,
    adjointEquiv_logScaledLattice, ← mixedIdealLogScale_neg,
    logScaledLattice_det, mixedIdealLogScale_sum, Real.exp_zero, one_mul,
    abs_inv, mixedIdealMatrix_abs_det, mixedIdealIndex_card]
  simp_rw [mixedPrimitiveCosetFourierWeight K I M hI hM χ hχ]
  change _ * _ * (∑' z : MixedConductorIndex K I M hI hM → ℤ,
    Complex.exp (-((Real.pi*t⁻¹ : ℝ) : ℂ) *
      ‖logScale (mixedIdealLogScale K (mixedConductorIdeal K I M hI hM) (-u))
        (adjointEquiv (mixedIdealMatrix K (mixedConductorIdeal K I M hI hM)).symm
          (euclideanInteger z))‖^2) * _) = _
  simp_rw [mixedDualIntegerEquiv_coordinates, ← Complex.ofReal_pow,
    mixedTraceDualFlow_norm_sq]
  congr 1
  exact (mixedDualIntegerEquiv K (mixedConductorIdeal K I M hI hM)).tsum_eq
    (fun β : (mixedTraceDualIdeal K (mixedConductorIdeal K I M hI hM)).val =>
      Complex.exp (-((Real.pi * t⁻¹ : ℝ) : ℂ) *
        ((∑ w : InfinitePlace K,
          ((w.mult : ℝ) * mixedPlaceWeight K (-u) w * w (β : K))^2 : ℝ) : ℂ)) *
      (χ⁻¹ (idealModuleDualResidue K I M hI hM β β.property) *
        idealTraceGaussSum K M χ))

end
end ArtinMatthews.VaryingKummerAnalytic
