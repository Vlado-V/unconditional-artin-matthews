module

public import ArtinMatthews.SourceKPIntegralMatrixTopology
public import ArtinMatthews.SourceKPIntegralGroup
public import ArtinMatthews.SourceFiniteKPTameUnits
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

/-! The topological integral matrix group agrees with the actual valuation predicate. -/

set_option relaxedAutoImplicit false

namespace ArtinMatthews
open NumberField IsDedekindDomain Topology Matrix
open scoped NumberField MatrixGroups
noncomputable section

variable (K : Type) [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K))
local notation "L" => P.adicCompletion K
local notation "O" => P.adicCompletionIntegers K

lemma sourceKPIntegralMatrixMap_integral (g : GL (Fin 2) O) :
    SourceKPIntegralMatrix (sourceKPFiniteVal K P) (sourceKPIntegralMatrixMap K P g) := by
  refine ⟨?_, ?_⟩
  · intro i j
    exact (g.val i j).property
  · change sourceKPFiniteVal K P
      (GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap O L) g) : L) = 1
    rw [GeneralLinearGroup.map_det]
    change sourceKPFiniteVal K P ((GeneralLinearGroup.det g : O) : L) = 1
    exact (HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one
      (K := K) (v := P)).mp (GeneralLinearGroup.det g).isUnit

lemma sourceKPIntegralMatrixMap_mem_range (g : GL (Fin 2) L) :
    g ∈ Set.range (sourceKPIntegralMatrixMap K P) ↔
      SourceKPIntegralMatrix (sourceKPFiniteVal K P) g := by
  constructor
  · rintro ⟨a, rfl⟩
    exact sourceKPIntegralMatrixMap_integral K P a
  · intro hg
    rw [sourceKPIntegralMatrixMap_range]
    exact ⟨hg.entries, (sourceKPIntegralMatrix_inv _ hg).entries⟩

lemma sourceKPIntegralMatrixMap_range_eq :
    Set.range (sourceKPIntegralMatrixMap K P) = (sourceKPIntegralGroup (sourceKPFiniteVal K P) : Set (GL (Fin 2) L)) := by
  ext g
  exact sourceKPIntegralMatrixMap_mem_range K P g

end
end ArtinMatthews
