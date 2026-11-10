module

public import ArtinMatthews.CubicReciprocityNonprincipalCharacterBase
public import ArtinMatthews.CubicThetaResidueReduction
public import ArtinMatthews.CubicThetaWeightedCuspLimit
public import ArtinMatthews.CubicReciprocityNonprincipalCharacter
public import ArtinMatthews.CubicThetaHolomorphicLattice
public import ArtinMatthews.CubicThetaInfiniteCusp
public import ArtinMatthews.CubicThetaRationalCusps
public import ArtinMatthews.CubicThetaResidueActual
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

/-!
All rational cusp limits for the actual nonprincipal cubic numerator Hecke
theta. Rational phase cancellation is proved arithmetically, not assumed.
This module does not assert the remaining congruence transformation law.
-/
noncomputable section
namespace ArtinMatthews

open scoped BigOperators MatrixGroups Topology
open Complex UpperHalfPlane Filter OAI OAI.SevenEighths

/-- Every enlarged rational coordinate period gives the same actual ideal theta. -/
theorem cubicThetaActual_weight_eq_six (A : ℤ) (hA : A ≠ 0)
    (hnoncube : ¬ ∃ y : OAI.CubicFirstMoment.Eisenstein,
      y ^ 3 = (A : OAI.CubicFirstMoment.Eisenstein))
    (M : ℕ) [NeZero M] (hdiv : 9 * A ∣ (M : ℤ)) (τ : ℍ) :
    weightedEisensteinTheta
      (cubicThetaCoordinateWeight (cubicNumeratorHeckeCharacter A hA) M) τ =
        6 * heckeTheta (cubicNumeratorHeckeCharacter A hA) τ := by
  rw [← periodicGaussian_eq_six_heckeTheta (cubicNumeratorHeckeCharacter A hA)
    (cubicNumeratorHeckeCharacter_nonprincipal A hA hnoncube) τ]
  unfold weightedEisensteinTheta eisensteinWeightedGaussian
  apply tsum_congr
  intro n
  rw [cubicThetaActual_periodicCoeff A hA M hdiv,
    HeckeFamily.periodicCoeff_eq_elementCoeff]

/-- The actual cubic Hecke theta vanishes at every rational cusp after the
weight-one normalization, uniformly over the full real direction. -/
theorem tendsto_cubicNumeratorHeckeTheta_cusp (A : ℤ) (hA : A ≠ 0)
    (hnoncube : ¬ ∃ y : OAI.CubicFirstMoment.Eisenstein,
      y ^ 3 = (A : OAI.CubicFirstMoment.Eisenstein)) (γ : SL(2, ℤ)) :
    Tendsto (fun τ : ℍ => heckeTheta (cubicNumeratorHeckeCharacter A hA) (γ • τ) /
      ((γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ))) atImInfty (𝓝 0) := by
  by_cases hc : γ 1 0 = 0
  · exact tendsto_heckeTheta_cusp_of_lowerLeft_zero _ γ hc
  let M : ℕ := (9 * A * γ 1 0).natAbs
  have hM : M ≠ 0 := Int.natAbs_ne_zero.mpr
    (mul_ne_zero (mul_ne_zero (by norm_num) hA) hc)
  let : NeZero M := ⟨hM⟩
  have hdiv : 9 * A ∣ (M : ℤ) := by
    change 9 * A ∣ ((9 * A * γ 1 0).natAbs : ℤ)
    rw [Int.natCast_natAbs, dvd_abs]
    exact ⟨γ 1 0, rfl⟩
  have hcdiv : γ 1 0 ∣ (M : ℤ) := by
    change γ 1 0 ∣ ((9 * A * γ 1 0).natAbs : ℤ)
    rw [Int.natCast_natAbs, dvd_abs]
    exact ⟨9 * A, by ring⟩
  obtain ⟨k, hk⟩ := hcdiv
  have hlim := tendsto_weightedEisensteinTheta_cusp_of_twist_sum_zero
    (cubicThetaCoordinateWeight (cubicNumeratorHeckeCharacter A hA) M) γ hc k hk
      (cubicThetaActual_rationalTwist_sum_eq_zero A hA hnoncube M hdiv (γ 0 0 * k))
  have hscaled := hlim.div_const (6 : ℂ)
  have he : (fun τ : ℍ => weightedEisensteinTheta
      (cubicThetaCoordinateWeight (cubicNumeratorHeckeCharacter A hA) M) (γ • τ) /
        ((γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ)) / 6) =
      (fun τ : ℍ => heckeTheta (cubicNumeratorHeckeCharacter A hA) (γ • τ) /
        ((γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ))) := by
    funext τ
    rw [cubicThetaActual_weight_eq_six A hA hnoncube M hdiv]
    ring
  simpa only [he, zero_div] using hscaled

/-- A nonconstant character of the actual cubic Galois group supplies the
noncube condition needed above; no cusp cancellation is an extra input. -/
theorem cubicFourier_heckeTheta_cusp {S : Finset ℤ}
    (χ : AddChar (Additive (integerCubicGaloisGroup S)) ℂ) (hχ : χ ≠ 0)
    {A : ℤ} (hA : A ≠ 0) {R : integerCubicField S} (hR0 : R ≠ 0)
    (hR : R ^ 3 = (A : integerCubicField S))
    (hrep : ∀ σ : integerCubicGaloisGroup S,
      χ (Additive.ofMul σ) = ((σ.val R / R : integerCubicField S) : ℂ))
    (γ : SL(2, ℤ)) :
    Tendsto (fun τ : ℍ => heckeTheta (cubicNumeratorHeckeCharacter A hA) (γ • τ) /
      ((γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ))) atImInfty (𝓝 0) :=
  tendsto_cubicNumeratorHeckeTheta_cusp A hA
    (cubicFourier_radical_not_cube_in_cubicMoment χ hχ hR0 hR hrep) γ

end ArtinMatthews
