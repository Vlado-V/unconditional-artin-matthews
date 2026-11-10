module

public import ArtinMatthews.VaryingKummerAnalyticIdealModulePeriodicWeights
public import ArtinMatthews.VaryingKummerAnalyticMixedPrimitiveThetaCosets
public import ArtinMatthews.VaryingKummerAnalyticMixedPeriodicTheta
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Entire Mellin transforms of actual arbitrary-ideal conductor theta.
The genuine quotient coordinate gives a periodic weight of period Norm(M),
whose zero and constant Fourier modes vanish for nontrivial characters. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Module MeasureTheory Set
open NumberField.Units NumberField.Units.dirichletUnitTheorem
open ArtinMatthews.ReusedTheta
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable (I M : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hM : M ≠ ⊥)

private lemma modulusScaledBasis_logScaledLattice {d : Type*} [Fintype d]
    (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d) (N : ℕ) [NeZero N] (u : d → ℝ) :
    modulusScaledBasis (logScaledLattice B u) N = logScaledLattice (modulusScaledBasis B N) u := by
  ext x
  rfl

theorem mixedPrimitiveTheta_eq_periodic [NeZero M.absNorm]
    (χ : MulChar ((𝓞 K) ⧸ M) ℂ) (u : logSpace K) (t : ℝ) :
    mixedPrimitiveTheta K I M hI hM χ u t =
      normalizedPeriodicTheta
        (logScaledLattice (modulusScaledBasis
          (mixedIdealMatrix K (integralIdealFractionalUnit I hI)) M.absNorm)
          (mixedIdealLogScale K (integralIdealFractionalUnit I hI) u))
        M.absNorm (idealModuleCharacterWeight I M hI hM (mixedIntegralIdealBasis K I hI) χ) t := by
  rw [← modulusScaledBasis_logScaledLattice]
  unfold mixedPrimitiveTheta normalizedPeriodicTheta periodicLatticeTheta
  rw [← (mixedIntegralIdealBasis K I hI).equivFun.symm.toEquiv.tsum_eq]
  apply tsum_congr
  intro z
  simp only [LinearEquiv.coe_toEquiv, modulusScaledBasis_cancel]
  rw [← idealModuleCharacterWeight_coordinates I M hI hM (mixedIntegralIdealBasis K I hI) χ z]
  congr 1
  have hn := mixedIntegralIdealFlow_norm_sq K I hI
    ((mixedIntegralIdealBasis K I hI).equivFun.symm z) u
  simp only [LinearEquiv.apply_symm_apply] at hn
  rw [← Complex.ofReal_pow, hn]
  unfold mixedComplexArchGaussian
  congr 1
  push_cast
  ring

theorem mixedPrimitiveTheta_boundedAverage_entire
    (χ : MulChar ((𝓞 K) ⧸ M) ℂ) (hχ : χ ≠ 1)
    {S : Set (logSpace K)} (hS : MeasurableSet S) (hbd : Bornology.IsBounded S) :
    Differentiable ℂ (mellin (fun t => ∫ u in S, mixedPrimitiveTheta K I M hI hM χ u t)) := by
  let : NeZero M.absNorm := ⟨fun h => hM (Ideal.absNorm_eq_zero_iff.mp h)⟩
  have H : (fun t => ∫ u in S, mixedPrimitiveTheta K I M hI hM χ u t) =
      (fun t => ∫ u in S, normalizedPeriodicTheta
        (logScaledLattice (modulusScaledBasis
          (mixedIdealMatrix K (integralIdealFractionalUnit I hI)) M.absNorm)
          (mixedIdealLogScale K (integralIdealFractionalUnit I hI) u))
        M.absNorm (idealModuleCharacterWeight I M hI hM (mixedIntegralIdealBasis K I hI) χ) t) := by
    funext t
    apply integral_congr_ae
    filter_upwards [] with u
    exact mixedPrimitiveTheta_eq_periodic K I M hI hM χ u t
  rw [H]
  exact mixedPeriodicTheta_boundedAverage_entire K (integralIdealFractionalUnit I hI) _ M.absNorm _
    (idealModuleCharacterWeight_zero I M hI hM _ χ hχ)
    (idealModuleCharacterWeight_sum_zero I M hI hM _ χ hχ) hS hbd

theorem mixedPrimitiveTheta_unitAverage_entire
    (χ : MulChar ((𝓞 K) ⧸ M) ℂ) (hχ : χ ≠ 1) :
    Differentiable ℂ (mellin (fun t => ∫ u in mixedUnitLogDomain K,
      mixedPrimitiveTheta K I M hI hM χ u t)) :=
  mixedPrimitiveTheta_boundedAverage_entire K I M hI hM χ hχ
    (mixedUnitLogDomain_measurable K) (mixedUnitLogDomain_bounded K)

end
end ArtinMatthews.VaryingKummerAnalytic
