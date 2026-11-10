module

public import ArtinMatthews.CubicThetaAdelicIdentity
public import ArtinMatthews.ShiftedVoronoiCharacter
public import ArtinMatthews.CubicThetaScalarComparison
public import ArtinMatthews.CubicThetaUnweightedCongruence
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

/-! Exact integral-matrix specialization of the unweighted scalar comparison. -/
noncomputable section
namespace ArtinMatthews

open Complex UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups
open OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData

@[simp] theorem cubicTheta_rationalMatrix_entry (γ : SL(2, ℤ)) (i j : Fin 2) :
    (γ : SL(2, ℚ)) i j = (γ i j : ℚ) := by
  have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℚ => M i j)
    (Matrix.SpecialLinearGroup.coe_matrix_coe (R := ℚ) γ)
  exact h

theorem cubicTheta_rationalMatrix_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    (γ : SL(2, ℚ)) • τ = γ • τ := by
  apply UpperHalfPlane.ext
  erw [UpperHalfPlane.coe_specialLinearGroup_apply]

/-- The proved unweighted Γ₀(3) multiplier also holds under the literal
rational matrix used by the symplectic embedding. -/
theorem eisensteinHolomorphicTheta_rational_Gamma0_three (γ : SL(2, ℤ))
    (hγ : γ ∈ Gamma0 3) (τ : ℍ) :
    eisensteinHolomorphicTheta ((γ : SL(2, ℚ)) • τ) =
      cubicThetaNebentypus (γ 1 1) *
        (((γ : SL(2, ℚ)) 1 0 : ℂ) * τ + ((γ : SL(2, ℚ)) 1 1 : ℂ)) *
          eisensteinHolomorphicTheta τ := by
  simpa only [cubicTheta_rationalMatrix_smul, cubicTheta_rationalMatrix_entry,
    Rat.cast_intCast] using eisensteinHolomorphicTheta_Gamma0_three γ hγ τ

variable {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]

/-- The exact Γ₀ multiplier transfers to every test with the proved common
finite scalar. Arithmetic production of those scalar equations is separate. -/
theorem eisensteinTheta_integer_common_scalar_transform
    (D : WeilData (Fin 2) MpR MpF MpA) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 3)
    (M : ℕ) [NeZero M] (c : ℂ)
    (hbase : D.finiteAction (eisensteinSymplectic (γ : SL(2, ℚ)))
      (eisensteinFiniteTest (fun _ : Fin M × Fin M => (1 : ℂ))) =
        c • eisensteinFiniteTest (fun _ : Fin M × Fin M => (1 : ℂ)))
    (φ : finiteSchwartz (Fin 2))
    (hφ : D.finiteAction (eisensteinSymplectic (γ : SL(2, ℚ))) φ = c • φ) (τ : ℍ) :
    theta φ (eisensteinSiegel (γ • τ)) 0 =
      cubicThetaNebentypus (γ 1 1) * ((γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ)) *
        theta φ (eisensteinSiegel τ) 0 := by
  have h := eisensteinTheta_common_scalar_transform D (γ : SL(2, ℚ))
    (cubicThetaNebentypus (γ 1 1))
    (eisensteinHolomorphicTheta_rational_Gamma0_three γ hγ) M c hbase φ hφ τ
  simpa only [cubicTheta_rationalMatrix_smul, cubicTheta_rationalMatrix_entry,
    Rat.cast_intCast] using h

end ArtinMatthews
