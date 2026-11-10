module

public import ArtinMatthews.VaryingKummerAnalyticMixedPrimitiveGeneratorContinuation
public import ArtinMatthews.VaryingKummerAnalyticGrowth
public import ArtinMatthews.VaryingKummerAnalyticMixedPeriodicGrowth
public import ArtinMatthews.VaryingKummerAnalyticMixedPrimitiveThetaEntire
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

/-! Actual subquadratic growth of primitive theta Mellin transforms and their
finite class completion. No functional equation or growth bound is assumed. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Module MeasureTheory Set
open NumberField.Units NumberField.Units.dirichletUnitTheorem
open ArtinMatthews.ReusedTheta ArtinMatthews.ReusedGrowth
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable (I M : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hM : M ≠ ⊥)

theorem mixedPrimitiveTheta_boundedAverage_hasSubquadraticGrowth
    (χ : MulChar ((𝓞 K) ⧸ M) ℂ) (hχ : χ ≠ 1)
    {S : Set (logSpace K)} (hS : MeasurableSet S) (hbd : Bornology.IsBounded S) :
    HasSubquadraticGrowth (mellin (fun t => ∫ u in S, mixedPrimitiveTheta K I M hI hM χ u t)) := by
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
  exact mixedPeriodicTheta_boundedAverage_hasSubquadraticGrowth K (integralIdealFractionalUnit I hI) _ M.absNorm _
    (idealModuleCharacterWeight_zero I M hI hM _ χ hχ)
    (idealModuleCharacterWeight_sum_zero I M hI hM _ χ hχ) hS hbd

theorem mixedPrimitiveTheta_unitAverage_hasSubquadraticGrowth
    (χ : MulChar ((𝓞 K) ⧸ M) ℂ) (hχ : χ ≠ 1) :
    HasSubquadraticGrowth (mellin (fun t => ∫ u in mixedUnitLogDomain K,
      mixedPrimitiveTheta K I M hI hM χ u t)) :=
  mixedPrimitiveTheta_boundedAverage_hasSubquadraticGrowth K I M hI hM χ hχ
    (mixedUnitLogDomain_measurable K) (mixedUnitLogDomain_bounded K)

namespace EvenIdealRayCharacter
variable {K M} (ψ : EvenIdealRayCharacter K M)

theorem generatorCompletedMellin_hasSubquadraticGrowth
    (G : ClassGroup (𝓞 K) → Ideal (𝓞 K)) (hG : ∀ c, G c ≠ ⊥)
    (hres : ψ.residue ≠ 1) :
    HasSubquadraticGrowth (ψ.generatorCompletedMellin hM G hG) := by
  apply (hasSubquadraticGrowth_const (mixedResidueIdealMellinFactor K)⁻¹).mul
  apply HasSubquadraticGrowth.finset_sum Finset.univ
  intro c _
  apply (hasSubquadraticGrowth_const _).mul
  apply (hasSubquadraticGrowth_const_cpow (fractionalIdeal_absNorm_pos _)).mul
  have H0 := mixedPrimitiveTheta_unitAverage_hasSubquadraticGrowth K
    (rayClassRepresentative K 1 c) M (rayClassRepresentative_ne_bot K 1 c) hM ψ.residue hres
  have H := H0.comp_affine ((Module.finrank ℚ K:ℂ)/2) 0
  apply H.congr
  intro s
  congr 1
  ring

theorem scaledGeneratorCompletedMellin_hasSubquadraticGrowth
    (G : ClassGroup (𝓞 K) → Ideal (𝓞 K)) (hG : ∀ c, G c ≠ ⊥)
    (hres : ψ.residue ≠ 1) {A : ℝ} (hA : 0 < A) :
    HasSubquadraticGrowth (fun s => (A:ℂ)^s * ψ.generatorCompletedMellin hM G hG s) :=
  (hasSubquadraticGrowth_const_cpow hA).mul
    (ψ.generatorCompletedMellin_hasSubquadraticGrowth hM G hG hres)

end EvenIdealRayCharacter

end
end ArtinMatthews.VaryingKummerAnalytic
