module

public import ArtinMatthews.VaryingKummerAnalyticMixedPeriodicTheta


set_option backward.privateInPublic true
@[expose] public section

/-! Actual integral-ideal residue-character theta in arbitrary signature. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Module MeasureTheory Set
open NumberField.Units NumberField.Units.dirichletUnitTheorem
open ArtinMatthews.ReusedTheta
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)

/-- Literal theta series over elements of the integral ideal, weighted by
the actual finite residue character and canonical mixed Gaussian matrix. -/
def mixedIdealResidueFlowTheta (N : ℕ)
    (χ : MulChar ((𝓞 K) ⧸ rationalModulusIdeal (𝓞 K) N) ℂ)
    (u : logSpace K) (t : ℝ) : ℂ :=
  idealCharacterTheta I (mixedIntegralIdealBasis K I hI)
    (logScaledLattice (mixedIdealMatrix K (integralIdealFractionalUnit I hI))
      (mixedIdealLogScale K (integralIdealFractionalUnit I hI) u)) N χ t

private lemma modulusScaledBasis_logScaledLattice {d : Type*} [Fintype d]
    (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d) (N : ℕ) [NeZero N] (u : d → ℝ) :
    modulusScaledBasis (logScaledLattice B u) N = logScaledLattice (modulusScaledBasis B N) u := by
  ext x
  rfl

theorem mixedIdealResidueFlowTheta_boundedAverage_entire
    (N : ℕ) [NeZero N] (hcop : IsCoprime I (rationalModulusIdeal (𝓞 K) N))
    (χ : MulChar ((𝓞 K) ⧸ rationalModulusIdeal (𝓞 K) N) ℂ) (hχ : χ ≠ 1)
    {S : Set (logSpace K)} (hS : MeasurableSet S) (hbd : Bornology.IsBounded S) :
    Differentiable ℂ (mellin (fun t => ∫ u in S,mixedIdealResidueFlowTheta K I hI N χ u t)) := by
  let J := integralIdealFractionalUnit I hI
  let B := mixedIdealMatrix K J
  let bI := mixedIntegralIdealBasis K I hI
  let bR := mixedIntegralRingBasis K I hI
  have H : (fun t => ∫ u in S,mixedIdealResidueFlowTheta K I hI N χ u t) =
      (fun t => ∫ u in S,normalizedPeriodicTheta
        (logScaledLattice (modulusScaledBasis B N) (mixedIdealLogScale K J u))
          N (idealCharacterWeight I bI N χ) t) := by
    funext t
    apply integral_congr_ae
    filter_upwards [] with u
    have Htheta := idealCharacterTheta_eq_periodic I bI
      (logScaledLattice B (mixedIdealLogScale K J u)) N
      (show MulChar ((𝓞 K) ⧸ ReusedTheta.rationalModulusIdeal (𝓞 K) N) ℂ from χ) t
    simpa only [mixedIdealResidueFlowTheta, J, B, bI, modulusScaledBasis_logScaledLattice] using Htheta
  rw [H]
  exact mixedPeriodicTheta_boundedAverage_entire K J _ N _
    (idealCharacterWeight_zero I bI N χ hχ)
    (idealCharacterWeight_sum_zero I bI bR N hcop χ hχ) hS hbd

/-- Entire Mellin transform after averaging over the actual full Dirichlet
unit-log fundamental domain, without a totally-real hypothesis. -/
theorem mixedIdealResidueFlowTheta_unitAverage_entire
    (N : ℕ) [NeZero N] (hcop : IsCoprime I (rationalModulusIdeal (𝓞 K) N))
    (χ : MulChar ((𝓞 K) ⧸ rationalModulusIdeal (𝓞 K) N) ℂ) (hχ : χ ≠ 1) :
    Differentiable ℂ (mellin (fun t => ∫ u in mixedUnitLogDomain K,
      mixedIdealResidueFlowTheta K I hI N χ u t)) :=
  mixedIdealResidueFlowTheta_boundedAverage_entire K I hI N hcop χ hχ
    (mixedUnitLogDomain_measurable K) (mixedUnitLogDomain_bounded K)

end
end ArtinMatthews.VaryingKummerAnalytic
