module

public import ArtinMatthews.VaryingKummerAnalyticRayIdealClassSeries
public import ArtinMatthews.VaryingKummerAnalyticMixedPrimitiveThetaCosets
public import ArtinMatthews.VaryingKummerAnalyticMixedPrimitiveThetaConvergence
public import ArtinMatthews.VaryingKummerAnalyticMixedResidueUnfolding
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
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Exact nonzero-element and unit-orbit unfolding at an arbitrary ideal
conductor. The theta constant χ(0) is retained, including conductor one. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Module MeasureTheory Set Filter
open NumberField.Units NumberField.Units.dirichletUnitTheorem
open ArtinMatthews.ReusedTheta
open scoped NumberField nonZeroDivisors Classical BigOperators ENNReal
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem mixedPrimitiveTheta_nonzero (I M : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hM : M ≠ ⊥)
    (χ : MulChar ((𝓞 K) ⧸ M) ℂ) (u : logSpace K) {t : ℝ} (ht : 0 < t) :
    mixedPrimitiveTheta K I M hI hM χ u t - χ 0 =
      ∑' a : nonzeroIdealElements (integralIdealFractionalUnit I hI),
        idealModuleResidueElementWeight I M hI hM χ a * mixedComplexArchGaussian K a.1.1 t u := by
  let F := fun a : I => χ (idealResidueCoordinate I M hI hM a) *
    mixedComplexArchGaussian K ((a:𝓞 K):K) t u
  let : NeZero M := ⟨hM⟩
  have HS := mixedPrimitiveTheta_summable K I M hI hM χ u ht
  have Hsum : (∑' a, F a) = F 0 + ∑' a : {a : I // a ≠ 0}, F a.val := by
    rw [HS.tsum_eq_add_tsum_ite (0:I)]
    congr 1
    change (∑' a : I, if a = 0 then 0 else F a) = ∑' a : ({a : I | a ≠ 0} : Set I), F a
    rw [tsum_subtype]
    simp only [Set.indicator_apply,Set.mem_ofPred_eq,ite_not]
  have H0 : F 0 = χ 0 := by
    simp [F,mixedComplexArchGaussian,mixedArchEnergy]
  change (∑' a, F a) - χ 0 = _
  rw [Hsum,H0,add_sub_cancel_left,← (integralIdealNonzeroEquiv K I hI).tsum_eq]
  apply tsum_congr
  intro a
  have HA : idealModuleIntegerElement K I hI ((integralIdealNonzeroEquiv K I hI) a) = a.val := by
    apply Subtype.ext
    apply NumberField.RingOfIntegers.coe_injective
    change ((idealModuleIntegerElement K I hI ((integralIdealNonzeroEquiv K I hI) a)).val:K) = _
    rw [idealModuleIntegerElement_coe]
    rfl
  simp only [idealModuleResidueElementWeight,HA,F]
  rfl

theorem mixedPrimitiveWeightedGaussian_summable (I M : Ideal (𝓞 K))
    (hI : I ≠ ⊥) (hM : M ≠ ⊥) (χ : MulChar ((𝓞 K) ⧸ M) ℂ)
    (u : logSpace K) {t : ℝ} (ht : 0 < t) :
    Summable (fun a : nonzeroIdealElements (integralIdealFractionalUnit I hI) =>
      idealModuleResidueElementWeight I M hI hM χ a * mixedComplexArchGaussian K a.1.1 t u) := by
  apply (mixedComplexArchGaussian_ideal_summable_norm K
    (integralIdealFractionalUnit I hI) u ht).of_norm_bounded
  intro a
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _)
    (idealModuleResidueElementWeight_norm_le_one I M hI hM χ a)

theorem mixedPrimitiveTheta_ideal_units (I M : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hM : M ≠ ⊥)
    (χ : MulChar ((𝓞 K) ⧸ M) ℂ)
    (hunit : ∀ z : (𝓞 K)ˣ, χ (Ideal.Quotient.mk M (z:𝓞 K)) = 1)
    (u : logSpace K) {t : ℝ} (ht : 0 < t) :
    mixedPrimitiveTheta K I M hI hM χ u t - χ 0 =
      ∑' J : integralIdealClassFiber (integralIdealFractionalUnit I hI),
        idealModuleResidueCoefficient I M hI hM χ J *
          ∑' z : (𝓞 K)ˣ, mixedComplexArchGaussian K
            ((z:K)*(idealElementRepresentative _ J).1.1) t u := by
  rw [mixedPrimitiveTheta_nonzero K I M hI hM χ u ht]
  let F := fun a : nonzeroIdealElements (integralIdealFractionalUnit I hI) =>
    idealModuleResidueElementWeight I M hI hM χ a * mixedComplexArchGaussian K a.1.1 t u
  let e := idealElementDecomposition (integralIdealFractionalUnit I hI)
  have HS : Summable (fun x => F (e x)) := e.summable_iff.mpr
    (mixedPrimitiveWeightedGaussian_summable K I M hI hM χ u ht)
  rw [← e.tsum_eq F,HS.tsum_sigma]
  apply tsum_congr
  intro J
  rw [← tsum_mul_left]
  apply tsum_congr
  intro z
  change idealModuleResidueElementWeight I M hI hM χ
    (idealElementUnitAction _ z (idealElementRepresentative _ J)) * _ = _
  rw [idealModuleResidueElementWeight_unitAction,hunit,one_mul]
  rfl

end
end ArtinMatthews.VaryingKummerAnalytic
