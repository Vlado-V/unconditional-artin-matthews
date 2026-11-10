module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.PivotChoices
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
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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
public import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.Units


set_option backward.privateInPublic true
@[expose] public section

/-! # Matrix Pivot -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.MatrixPivot.CM

noncomputable section

/-! Assemble local zero-one row corrections into an adelic row
correction whose pivot is an actual unit of the finite adelic ring. -/

open scoped Classical _root_.Matrix RestrictedProduct
open Filter
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.PivotChoices.CM

variable {I : Type*} [Fintype I]

def rowCorrection (A : (Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)ˣ) (i : I) : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf := fun j =>
  ⟨fun v => PivotChoices.CM.correction A v i j, Filter.Eventually.of_forall fun v => by
    dsimp only
    rcases PivotChoices.CM.correction_binary A v i j with h | h
    · rw [h]; exact (v.adicCompletionIntegers ℚ).zero_mem
    · rw [h]; exact (v.adicCompletionIntegers ℚ).one_mem⟩

theorem rowCorrection_zero (A : (Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)ˣ) (i : I) : rowCorrection A i i = 0 := by
  apply DFunLike.ext
  intro v
  exact PivotChoices.CM.correction_zero A v i

def pivotValue (A : (Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)ˣ) (i : I) : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf :=
  A.val i i + ∑ j, rowCorrection A i j * A.val j i

theorem pivotValue_eval (A : (Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)ˣ) (i : I) (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) :
    SymplecticLocal.CM.localEval v (pivotValue A i) = PivotChoices.CM.pivot A v i := by
  rw [pivotValue, map_add, map_sum]
  change A.val i i v + _ = (IntegralMatrixUnit.CM.localUnit A v).val i i + _
  congr 1

theorem pivotValue_unit (A : (Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)ˣ) (i : I) : IsUnit (pivotValue A i) := by
  apply Adelic.Units.CM.isUnit_of_local
  · intro v
    change SymplecticLocal.CM.localEval v (pivotValue A i) ≠ 0
    rw [pivotValue_eval]
    exact (PivotChoices.CM.pivot_unit A v i).ne_zero
  · filter_upwards [IntegralMatrixUnit.CM.eventually_integral A] with v hv
    change (SymplecticLocal.CM.localEval v (pivotValue A i))⁻¹ ∈ v.adicCompletionIntegers ℚ
    rw [pivotValue_eval]
    exact PivotChoices.CM.inverse_integral A v hv i

theorem exists_row_correction (A : (Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)ˣ) (i : I) :
    ∃ c : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf, c i = 0 ∧ IsUnit (A.val i i + ∑ j, c j * A.val j i) :=
  ⟨rowCorrection A i, rowCorrection_zero A i, pivotValue_unit A i⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.MatrixPivot.CM
