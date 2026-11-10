module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.ScalarComparison
public import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.MatrixUnitsMap
public import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.LeviOscillator
public import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BlockMatrixUnits
public import OAI.RepresentationTheory.Weil.Local.LinearIntertwiner
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

/-! # Levi Operators -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Rational.LeviOperators.CM

noncomputable section

/-! Actual real and finite oscillator operators above a rational Levi
matrix. Their nonzero scalar factors are retained explicitly. -/

open scoped Classical _root_.Matrix
open _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.ScalarComparison.CM
variable (n : ℕ)

def realUnit (A : (Matrix (Fin n) (Fin n) ℚ)ˣ) : (Matrix (Fin n) (Fin n) ℝ)ˣ :=
  MatrixUnitsMap.CM.map (Equiv.refl (Fin n)) (algebraMap ℚ ℝ) A

abbrev finiteMatrixMonoid : Monoid (Matrix (Fin n) (Fin n) RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :=
  letI : DecidableEq (Fin n) := Classical.decEq (Fin n)
  inferInstance

def finiteUnit (A : (Matrix (Fin n) (Fin n) ℚ)ˣ) :
    @Units (Matrix (Fin n) (Fin n) RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (finiteMatrixMonoid n) :=
  @MatrixUnitsMap.CM.map (Fin n) (Fin n) ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf _ _ inferInstance (Classical.decEq _) _ _
    (Equiv.refl (Fin n)) (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) A

def realInput (A : (Matrix (Fin n) (Fin n) ℚ)ˣ) : (Matrix (Fin n) (Fin n) ℝ)ˣ :=
  (BlockMatrixUnits.CM.transposeUnit (realUnit n A))⁻¹

def realOscillator (A : (Matrix (Fin n) (Fin n) ℚ)ˣ) : Adelic.ScalarComparison.CM.RealOscillator n :=
  RepresentationTheory.Weil.Local.LinearIntertwiner.Construction.linearOscillator (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) (realInput n A)

def finiteOscillator (A : (Matrix (Fin n) (Fin n) ℚ)ˣ) : Adelic.ScalarComparison.CM.FiniteOscillator n :=
  Finite.LeviOscillator.CM.leviOscillator (finiteUnit n A)

theorem realUnit_val (A : (Matrix (Fin n) (Fin n) ℚ)ˣ) :
    (realUnit n A).val = A.val.map (algebraMap ℚ ℝ) := rfl

theorem realUnit_inv_val (A : (Matrix (Fin n) (Fin n) ℚ)ˣ) :
    ((realUnit n A)⁻¹).val = (A⁻¹).val.map (algebraMap ℚ ℝ) := by
  apply Matrix.ext
  intro i j
  exact MatrixUnitsMap.CM.map_inv_val (Equiv.refl (Fin n)) (algebraMap ℚ ℝ) A i j

theorem finiteUnit_val (A : (Matrix (Fin n) (Fin n) ℚ)ˣ) :
    (@Units.val _ (finiteMatrixMonoid n) (finiteUnit n A)) = A.val.map (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) := rfl

theorem finiteUnit_inv_val (A : (Matrix (Fin n) (Fin n) ℚ)ˣ) :
    (@Units.val _ (finiteMatrixMonoid n) ((finiteUnit n A)⁻¹)) = (A⁻¹).val.map (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) := by
  apply Matrix.ext
  intro i j
  exact @MatrixUnitsMap.CM.map_inv_val (Fin n) (Fin n) ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf _ _ inferInstance (Classical.decEq _) _ _
    (Equiv.refl (Fin n)) (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) A i j

theorem realInput_val (A : (Matrix (Fin n) (Fin n) ℚ)ˣ) :
    (realInput n A).val = ((realUnit n A)⁻¹).val.transpose := rfl

theorem realInput_inv_val (A : (Matrix (Fin n) (Fin n) ℚ)ˣ) :
    ((realInput n A)⁻¹).val = (realUnit n A).val.transpose := by
  unfold realInput
  rw [inv_inv]
  rfl

def realScalar (A : (Matrix (Fin n) (Fin n) ℚ)ˣ) : ℂ :=
  ((Real.sqrt (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.localModulus ℝ (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.determinantUnit ℝ (realInput n A))))⁻¹ : ℂ)

def finiteScalar (A : (Matrix (Fin n) (Fin n) ℚ)ˣ) : ℂ :=
  (Finite.UnitaryTransport.CM.scalar (Finite.LeviOscillator.CM.LinearCoordinates.coordinates (finiteUnit n A)) : ℂ)

theorem real_apply (A : (Matrix (Fin n) (Fin n) ℚ)ˣ) (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz (Fin n)) (x : Fin n → ℝ) :
    (Adelic.ScalarComparison.CM.realOperator n (realOscillator n A) f).val x =
      realScalar n A * f.val ((A.val.transpose.map (algebraMap ℚ ℝ)) *ᵥ x) := by
  change ((RepresentationTheory.Weil.Local.LinearIntertwiner.Construction.linearOscillator (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) (realInput n A)).val.2
    (HeckeCycles.Real.SchwartzComparison.CM.tests n f)).val x = _
  rw [RepresentationTheory.Weil.Local.LinearIntertwiner.Construction.linearOscillator_apply, realInput_inv_val, realUnit_val]
  rfl

theorem finite_apply (A : (Matrix (Fin n) (Fin n) ℚ)ˣ) (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin n)) (x : Fin n → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    (Finite.FiniteOscillator.CM.action (finiteOscillator n A) φ).val x =
      finiteScalar n A * φ.val ((A.val.transpose.map (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) *ᵥ x) := by
  change (Finite.LeviOscillator.CM.LinearCoordinates.operator (finiteUnit n A) φ).val x = _
  rw [Finite.LeviOscillator.CM.LinearCoordinates.operator_apply, finiteUnit_val]
  rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Rational.LeviOperators.CM
