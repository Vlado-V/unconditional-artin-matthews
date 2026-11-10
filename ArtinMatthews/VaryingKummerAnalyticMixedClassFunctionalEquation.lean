module

public import ArtinMatthews.VaryingKummerAnalyticRayUnramifiedClassXi
public import ArtinMatthews.VaryingKummerAnalyticMixedDedekindFunctionalEquation
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

/-! The genuine ideal-class character functional transform in arbitrary
signature. It follows from actual trace-dual ideal Poisson and the exact
class permutation; no Hecke functional equation is an input. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField FractionalIdeal
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

def inverseClassCharacter (χ : ClassGroup (𝓞 K) →* ℂ) : ClassGroup (𝓞 K) →* ℂ where
  toFun c := χ c⁻¹
  map_one' := by simp
  map_mul' a b := by simp [mul_comm]

omit [NumberField K] in
@[simp] theorem inverseClassCharacter_apply (χ : ClassGroup (𝓞 K) →* ℂ) (c : ClassGroup (𝓞 K)) :
    inverseClassCharacter K χ c = χ c⁻¹ := rfl

omit [NumberField K] in
theorem inverseClassCharacter_ne_one (χ : ClassGroup (𝓞 K) →* ℂ) (hχ : χ ≠ 1) :
    inverseClassCharacter K χ ≠ 1 := by
  intro H
  apply hχ
  ext c
  have h := congrArg (fun ψ : ClassGroup (𝓞 K) →* ℂ => ψ c⁻¹) H
  simpa only [inverseClassCharacter_apply,inv_inv,MonoidHom.one_apply] using h

def mixedClassRootNumber (χ : ClassGroup (𝓞 K) →* ℂ) : ℂ :=
  χ ((ClassGroup.mk K (mixedTraceDualIdeal K 1))⁻¹)

theorem mixedClassRootNumber_norm (χ : ClassGroup (𝓞 K) →* ℂ) :
    ‖mixedClassRootNumber K χ‖ = 1 := by
  let c := (ClassGroup.mk K (mixedTraceDualIdeal K 1))⁻¹
  have hc : 0 < orderOf c := orderOf_pos c
  have H := congrArg (fun z : ℂ => ‖z‖) (show χ c ^ orderOf c = 1 by
    rw [← map_pow,pow_orderOf_eq_one,map_one])
  simp only [norm_pow,norm_one] at H
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hc.ne').mp H

theorem mixedNormalizedIdealXi_weighted_reflection
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) :
    (mixedDiscriminantScale K : ℂ)^s * mixedNormalizedIdealXi K I s =
      (mixedDiscriminantScale K : ℂ)^(1-s) *
        mixedNormalizedIdealXi K (mixedTraceDualIdeal K I) (1-s) := by
  simpa only [mixedNormalizedIdealXi,mul_assoc] using mixedIdealUnitXi_weighted_reflection K I s

/-- Actual weighted class permutation gives the codifferent character
value as the common unit-modulus factor. -/
theorem mixedIdealClassXi_functional_equation (χ : ClassGroup (𝓞 K) →* ℂ) (s : ℂ) :
    (mixedDiscriminantScale K : ℂ)^s * mixedIdealClassXi K χ s =
      mixedClassRootNumber K χ * (mixedDiscriminantScale K : ℂ)^(1-s) *
        mixedIdealClassXi K (inverseClassCharacter K χ) (1-s) := by
  have hc (c : ClassGroup (𝓞 K)) :
      mixedNormalizedIdealXi K (mixedTraceDualIdeal K (classRepresentative K c)) (1-s) =
        mixedNormalizedIdealXi K (classRepresentative K (mixedTraceDualClassEquiv K c)) (1-s) := by
    exact congrFun (mixedNormalizedIdealXi_eq_of_class_eq K _ _
      ((mixedTraceDual_classRepresentative K c).trans
        (classRepresentative_spec K (mixedTraceDualClassEquiv K c)).symm)) (1-s)
  have hw (c : ClassGroup (𝓞 K)) : χ c⁻¹ = mixedClassRootNumber K χ *
      inverseClassCharacter K χ ((mixedTraceDualClassEquiv K c)⁻¹) := by
    simp only [inverseClassCharacter_apply,inv_inv,mixedTraceDualClassEquiv_apply,
      map_mul,mixedClassRootNumber]
    rw [← mul_assoc,← map_mul,inv_mul_cancel,map_one,one_mul]
  calc
    _ = (mixedDiscriminantScale K : ℂ)^(1-s) *
        ∑ c : ClassGroup (𝓞 K), χ c⁻¹ *
          mixedNormalizedIdealXi K (mixedTraceDualIdeal K (classRepresentative K c)) (1-s) := by
      unfold mixedIdealClassXi
      rw [Finset.mul_sum,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      calc
        _ = χ c⁻¹ * ((mixedDiscriminantScale K : ℂ)^s *
            mixedNormalizedIdealXi K (classRepresentative K c) s) := by ring
        _ = _ := by rw [mixedNormalizedIdealXi_weighted_reflection]; ring
    _ = (mixedDiscriminantScale K : ℂ)^(1-s) * (mixedClassRootNumber K χ *
        ∑ c : ClassGroup (𝓞 K), inverseClassCharacter K χ ((mixedTraceDualClassEquiv K c)⁻¹) *
          mixedNormalizedIdealXi K (classRepresentative K (mixedTraceDualClassEquiv K c)) (1-s)) := by
      simp_rw [hc,hw]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      ring
    _ = _ := by
      rw [(mixedTraceDualClassEquiv K).sum_comp (fun c =>
        inverseClassCharacter K χ c⁻¹ * mixedNormalizedIdealXi K (classRepresentative K c) (1-s))]
      unfold mixedIdealClassXi
      ring

end
end ArtinMatthews.VaryingKummerAnalytic
