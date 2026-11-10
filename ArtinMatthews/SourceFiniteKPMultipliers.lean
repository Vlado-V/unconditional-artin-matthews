module

public import ArtinMatthews.SourceFiniteKPHilbert
public import ArtinMatthews.SourceKubotaCoordinates
public import ArtinMatthews.SourceKubotaMultipliers
public import ArtinMatthews.SourceKubotaScalarMultipliers
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Actual finite-place evaluations for every factor in the source's
root, Weyl and Bruhat formulas. The cubic Hilbert character is supplied
by the constructed CFT pairing, not a premise. The global cocycle law
and the automorphic representation remain separate. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open scoped NumberField MatrixGroups
noncomputable section
variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K))

private theorem minusOneUnit_cube (F : Type*) [Field F] :
    sourceMinusOneUnit F ^ 3 = sourceMinusOneUnit F := by
  apply Units.ext
  simp [sourceMinusOneUnit, pow_succ]

theorem sourceFiniteKPHilbert_minus_left (a : (P.adicCompletion K)ˣ) :
    sourceFiniteKPHilbert K hζ P (sourceMinusOneUnit (P.adicCompletion K)) a = 1 := by
  have h := sourceFiniteKPHilbert_cube_left K hζ P (sourceMinusOneUnit (P.adicCompletion K)) a
  rw [minusOneUnit_cube] at h
  exact h

theorem sourceFiniteKPHilbert_minus_right (a : (P.adicCompletion K)ˣ) :
    sourceFiniteKPHilbert K hζ P a (sourceMinusOneUnit (P.adicCompletion K)) = 1 := by
  have h := sourceFiniteKPHilbert_cube_right K hζ P a (sourceMinusOneUnit (P.adicCompletion K))
  rw [minusOneUnit_cube] at h
  exact h

def sourceFiniteKP2Multiplier (g h : GL (Fin 2) (P.adicCompletion K)) :
    rootsOfUnity 3 (P.adicCompletion K) := sourceKP2Multiplier (sourceFiniteKPHilbert K hζ P) g h

theorem sourceFiniteKP2Multiplier_root_diagonal (x : P.adicCompletion K)
    (u : (P.adicCompletion K)ˣ) :
    sourceFiniteKP2Multiplier K hζ P (sourceGL2Upper x) (sourceGL2Diagonal u) = 1 ∧
    sourceFiniteKP2Multiplier K hζ P (sourceGL2Diagonal u) (sourceGL2Upper x) = 1 :=
  ⟨sourceKP2Multiplier_upper_diagonal _ x u, sourceKP2Multiplier_diagonal_upper _ x u⟩

theorem sourceFiniteKP2Multiplier_weyl_diagonal (u : (P.adicCompletion K)ˣ) :
    sourceFiniteKP2Multiplier K hζ P sourceGL2Weyl (sourceGL2Diagonal u) = 1 ∧
    sourceFiniteKP2Multiplier K hζ P (sourceGL2Diagonal u⁻¹) sourceGL2Weyl = 1 ∧
    sourceFiniteKP2Multiplier K hζ P (sourceGL2Diagonal u⁻¹ * sourceGL2Weyl)
      (GeneralLinearGroup.scalar (Fin 2) u) = 1 :=
  ⟨sourceKP2Multiplier_weyl_diagonal _ u (sourceFiniteKPHilbert_diag K hζ P)
      (sourceFiniteKPHilbert_minus_left K hζ P) (sourceFiniteKPHilbert_minus_right K hζ P),
    sourceKP2Multiplier_diagonal_weyl _ u⁻¹ (sourceFiniteKPHilbert_minus_right K hζ P),
    sourceKP2Multiplier_Weyl_scalar _ u (sourceFiniteKPHilbert_diag K hζ P)
      (sourceFiniteKPHilbert_minus_left K hζ P) (sourceFiniteKPHilbert_minus_right K hζ P)⟩

theorem sourceFiniteKP2Multiplier_bruhat (u : (P.adicCompletion K)ˣ) :
    sourceFiniteKP2Multiplier K hζ P sourceGL2Weyl (sourceGL2Upper (u : P.adicCompletion K)) = 1 ∧
    sourceFiniteKP2Multiplier K hζ P (sourceGL2Upper ((u : P.adicCompletion K)⁻¹))
      (sourceBruhatMiddle u) = 1 ∧
    sourceFiniteKP2Multiplier K hζ P
      (sourceGL2Upper ((u : P.adicCompletion K)⁻¹) * sourceBruhatMiddle u)
      (sourceGL2Lower ((u : P.adicCompletion K)⁻¹)) = 1 ∧
    sourceFiniteKP2Multiplier K hζ P (sourceGL2Diagonal (sourceBruhatDiagonal u))
      (GeneralLinearGroup.scalar (Fin 2) u) = 1 :=
  ⟨sourceKP2Multiplier_weyl_upper _ _, sourceKP2Multiplier_upper_middle _ _ u,
    sourceKP2Multiplier_Bruhat_last _ u (sourceFiniteKPHilbert_diag K hζ P)
      (sourceFiniteKPHilbert_minus_right K hζ P),
    sourceKP2Multiplier_Bruhat_scalar _ u (sourceFiniteKPHilbert_diag K hζ P)
      (sourceFiniteKPHilbert_minus_left K hζ P) (sourceFiniteKPHilbert_minus_right K hζ P)⟩

end
end ArtinMatthews
