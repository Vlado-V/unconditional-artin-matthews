module

public import ArtinMatthews.CubicReciprocityNonprincipalCharacterBase
public import ArtinMatthews.CubicThetaAdelicIdentity
public import ArtinMatthews.CubicThetaResidueReduction
public import ArtinMatthews.ShiftedVoronoiCharacter
public import ArtinMatthews.CubicThetaFiniteWeightInvariant
public import ArtinMatthews.CubicThetaFiniteWeightedAction
public import ArtinMatthews.CubicThetaIntegralScalarComparison
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.NumberTheory.SelbergSieve
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

/-! The actual cubic Hecke theta transformation, with every finite lattice,
coset, weight, and common scalar condition discharged. The representation is
explicit here; its genuine constructed specialization is a separate endpoint. -/
noncomputable section
namespace ArtinMatthews

open scoped MatrixGroups
open Complex UpperHalfPlane CongruenceSubgroup
open OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData

variable {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]

/-- The actual finite weighted theta has the exact quadratic nebentypus on
the indicated congruence subgroup. No scalar action is an assumption. -/
theorem cubicNumeratorFiniteTheta_transform
    (D : WeilData (Fin 2) MpR MpF MpA) (A : ℤ) (hA : A ≠ 0)
    (M : ℕ) [NeZero M] (heven : 2 ∣ M) (hdiv : 9 * A ∣ (M : ℤ))
    (γ : SL(2, ℤ)) (hc : 6 * (M : ℤ) ^ 2 ∣ γ 1 0) (τ : ℍ) :
    theta (eisensteinFiniteTest
      (cubicThetaCoordinateWeight (cubicNumeratorHeckeCharacter A hA) M))
        (eisensteinSiegel (γ • τ)) 0 =
      cubicThetaNebentypus (γ 1 1) * ((γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ)) *
        theta (eisensteinFiniteTest
          (cubicThetaCoordinateWeight (cubicNumeratorHeckeCharacter A hA) M))
            (eisensteinSiegel τ) 0 := by
  have hM : (M : ℤ) ∣ γ 1 0 :=
    (dvd_mul_of_dvd_right (dvd_pow_self (M : ℤ) (by decide : 2 ≠ 0)) 6).trans hc
  have h3 : (3 : ℤ) ∣ γ 1 0 :=
    (dvd_mul_of_dvd_left (by norm_num : (3 : ℤ) ∣ 6) ((M : ℤ) ^ 2)).trans hc
  have hγ : γ ∈ Gamma0 3 := Gamma0_mem.mpr
    ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h3)
  apply eisensteinTheta_integer_common_scalar_transform D γ hγ M
    (cubicThetaFiniteScalar D M γ)
  · exact cubicThetaFinite_residueTest_scalar D M heven γ hc (fun _ => 1)
      (fun _ => rfl)
  · exact cubicThetaFinite_residueTest_scalar D M heven γ hc _
      (eisensteinFiniteWeight_cubicNumerator_lowerRight A hA M hdiv γ (hdiv.trans hM))

/-- Genuine congruence covariance of the ideal theta attached to the actual
nonprincipal cubic numerator character, at the explicit level `6 M²`. -/
theorem cubicNumeratorHeckeTheta_transform
    (D : WeilData (Fin 2) MpR MpF MpA) (A : ℤ) (hA : A ≠ 0)
    (hnoncube : ¬ ∃ y : OAI.CubicFirstMoment.Eisenstein,
      y ^ 3 = (A : OAI.CubicFirstMoment.Eisenstein))
    (M : ℕ) [NeZero M] (heven : 2 ∣ M) (hdiv : 9 * A ∣ (M : ℤ))
    (γ : SL(2, ℤ)) (hc : 6 * (M : ℤ) ^ 2 ∣ γ 1 0) (τ : ℍ) :
    heckeTheta (cubicNumeratorHeckeCharacter A hA) (γ • τ) =
      cubicThetaNebentypus (γ 1 1) * ((γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ)) *
        heckeTheta (cubicNumeratorHeckeCharacter A hA) τ := by
  have h := cubicNumeratorFiniteTheta_transform D A hA M heven hdiv γ hc τ
  rw [theta_eisensteinFiniteTest_cubicNumerator_eq_six A hA hnoncube M hdiv,
    theta_eisensteinFiniteTest_cubicNumerator_eq_six A hA hnoncube M hdiv] at h
  linear_combination (1 / 6 : ℂ) * h

end ArtinMatthews
