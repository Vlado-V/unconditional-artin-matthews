module

public import ArtinMatthews.SourceKPCommRingDiagonal
public import ArtinMatthews.SourceKPFiniteCompactTwist
public import ArtinMatthews.SourceKPFiniteAdeleTorus
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
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! The actual Weyl matrix over the adele ring and the exact local
cochain values needed to conjugate the normalized torus. The
three products in the lifted Weyl identity all have phase one. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open scoped NumberField MatrixGroups Classical
noncomputable section

def sourceKPWeylMatrix (R : Type*) [CommRing R] : GL (Fin 2) R :=
  GeneralLinearGroup.mk'' !![0, 1; 1, 0] (by simp [Matrix.det_fin_two])

theorem sourceKPWeylMatrix_field (F : Type*) [Field F] : sourceKPWeylMatrix F = (sourceGL2Weyl : GL (Fin 2) F) := by
  apply Units.ext
  rfl

theorem sourceKPWeylMatrix_map {R T : Type*} [CommRing R] [CommRing T] (f : R →+* T) :
    GeneralLinearGroup.map f (sourceKPWeylMatrix R) = sourceKPWeylMatrix T := by
  apply GeneralLinearGroup.ext
  intro i j
  change f ((!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) R) i j) =
    (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) T) i j
  fin_cases i <;> fin_cases j <;> simp

theorem sourceKPWeylMatrix_square (R : Type*) [CommRing R] :
    sourceKPWeylMatrix R * sourceKPWeylMatrix R = 1 := by
  apply GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [sourceKPWeylMatrix, Matrix.mul_apply, Fin.sum_univ_two]

theorem sourceKPWeylMatrix_mul_diagonal {R : Type*} [CommRing R] (u : Rˣ) :
    sourceKPWeylMatrix R * sourceKPDiagonalHom R u =
      sourceKPDiagonalHom R u⁻¹ * sourceKPWeylMatrix R * GeneralLinearGroup.scalar (Fin 2) u := by
  apply GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [sourceKPWeylMatrix, sourceKPDiagonalHom, Matrix.mul_apply, Fin.sum_univ_two,
      GeneralLinearGroup.coe_scalar, Matrix.diagonal_apply]

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K))

theorem sourceKPFinitePhase_zero_right (g : GL (Fin 2) (P.adicCompletion K)) (hg : g 1 1 = 0) :
    sourceKPFinitePhase K hζ P g = 1 := by
  by_cases h6 : (6 : 𝓞 K) ∉ P.asIdeal
  · rw [sourceKPFinitePhase, ite_eq_left h6, sourceKPCompactPhase]
    simp [hg]
  · rw [sourceKPFinitePhase, ite_eq_right h6]

theorem sourceKPFinitePhase_weyl : sourceKPFinitePhase K hζ P sourceGL2Weyl = 1 :=
  sourceKPFinitePhase_zero_right K hζ P _ (by simp [sourceGL2Weyl])

private theorem sourceKPFiniteTwistedMultiplier_eq_of_phase_one (g h : GL (Fin 2) (P.adicCompletion K))
    (hg : sourceKPFinitePhase K hζ P g = 1) (hh : sourceKPFinitePhase K hζ P h = 1)
    (hgh : sourceKPFinitePhase K hζ P (g * h) = 1) :
    sourceKPFiniteTwistedMultiplier K hζ P g h = sourceFiniteKP2Multiplier K hζ P g h := by
  rw [sourceKPFiniteTwistedMultiplier, sourceKPCochainTwist, hg, hh, hgh, one_mul, one_mul, div_one]

theorem sourceKPFiniteTwistedMultiplier_weyl_diagonal (u : (P.adicCompletion K)ˣ) :
    sourceKPFiniteTwistedMultiplier K hζ P sourceGL2Weyl (sourceGL2Diagonal u) = 1 ∧
      sourceKPFiniteTwistedMultiplier K hζ P (sourceGL2Diagonal u⁻¹) sourceGL2Weyl = 1 ∧
      sourceKPFiniteTwistedMultiplier K hζ P (sourceGL2Diagonal u⁻¹ * sourceGL2Weyl)
        (GeneralLinearGroup.scalar (Fin 2) u) = 1 := by
  have hWD : sourceKPFinitePhase K hζ P (sourceGL2Weyl * sourceGL2Diagonal u) = 1 :=
    sourceKPFinitePhase_zero_right K hζ P _
      (by simp [sourceGL2Weyl, sourceGL2Diagonal, Matrix.mul_apply, Fin.sum_univ_two])
  have hDW : sourceKPFinitePhase K hζ P (sourceGL2Diagonal u⁻¹ * sourceGL2Weyl) = 1 :=
    sourceKPFinitePhase_zero_right K hζ P _
      (by simp [sourceGL2Weyl, sourceGL2Diagonal, Matrix.mul_apply, Fin.sum_univ_two])
  have hDWS : sourceKPFinitePhase K hζ P (sourceGL2Diagonal u⁻¹ * sourceGL2Weyl * GeneralLinearGroup.scalar (Fin 2) u) = 1 := by
    rw [← sourceGL2Weyl_mul_diagonal]
    exact hWD
  have h := sourceFiniteKP2Multiplier_weyl_diagonal K hζ P u
  exact ⟨(sourceKPFiniteTwistedMultiplier_eq_of_phase_one K hζ P _ _ (sourceKPFinitePhase_weyl K hζ P)
    (sourceKPFinitePhase_diagonal K hζ P u) hWD).trans h.1,
    (sourceKPFiniteTwistedMultiplier_eq_of_phase_one K hζ P _ _ (sourceKPFinitePhase_diagonal K hζ P u⁻¹)
      (sourceKPFinitePhase_weyl K hζ P) hDW).trans h.2.1,
    (sourceKPFiniteTwistedMultiplier_eq_of_phase_one K hζ P _ _ hDW
      (sourceKPFinitePhase_scalar K hζ P u) hDWS).trans h.2.2⟩

end
end ArtinMatthews
