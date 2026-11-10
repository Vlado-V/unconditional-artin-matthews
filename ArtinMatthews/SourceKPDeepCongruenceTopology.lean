module

public import ArtinMatthews.SourceKPDeepCongruence
public import ArtinMatthews.SourceKPIntegralMatrixTopology
public import ArtinMatthews.SourceKPLocalUnitTopology
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
public import Mathlib.Topology.Algebra.Ring.Compact
public import Mathlib.Topology.Connected.Separation
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual deep principal congruence subgroup is compact-open in GL₂. -/

set_option relaxedAutoImplicit false

namespace ArtinMatthews
open NumberField IsDedekindDomain IsLocalRing Topology Matrix
open scoped NumberField MatrixGroups
noncomputable section

variable (K : Type) [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K))
local notation "L" => P.adicCompletion K
local notation "O" => P.adicCompletionIntegers K

lemma sourceKPDeepIdeal_isOpen : IsOpen (sourceKPDeepIdeal K P : Set O) := by
  let : CompactSpace O := isCompact_iff_compactSpace.mp (sourceKPLocalIntegers_isCompact K P)
  exact IsLocalRing.isOpen_maximalIdeal_pow O (sixthLocalHenselDepth P)

lemma sourceKPDeepIntegralGroup_mem_iff (g : GL (Fin 2) O) :
    g ∈ sourceKPDeepIntegralGroup K P ↔
      ∀ i j, g i j - (1 : Matrix (Fin 2) (Fin 2) O) i j ∈ sourceKPDeepIdeal K P := by
  change GeneralLinearGroup.map (Ideal.Quotient.mk (sourceKPDeepIdeal K P)) g = 1 ↔ _
  constructor
  · intro hg i j
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub]
    have he := congrArg (fun a : GL (Fin 2) (O ⧸ sourceKPDeepIdeal K P) => a i j) hg
    change Ideal.Quotient.mk (sourceKPDeepIdeal K P) (g i j) =
      (1 : Matrix (Fin 2) (Fin 2) (O ⧸ sourceKPDeepIdeal K P)) i j at he
    rw [he]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  · intro hg
    apply Units.ext
    apply Matrix.ext
    intro i j
    have he := Ideal.Quotient.eq_zero_iff_mem.mpr (hg i j)
    rw [map_sub, sub_eq_zero] at he
    change Ideal.Quotient.mk (sourceKPDeepIdeal K P) (g i j) =
      (1 : Matrix (Fin 2) (Fin 2) (O ⧸ sourceKPDeepIdeal K P)) i j
    rw [he]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

lemma sourceKPDeepIntegralGroup_isOpen :
    IsOpen (sourceKPDeepIntegralGroup K P : Set (GL (Fin 2) O)) := by
  have he : (sourceKPDeepIntegralGroup K P : Set (GL (Fin 2) O)) =
      ⋂ i : Fin 2, ⋂ j : Fin 2,
        {g | g i j - (1 : Matrix (Fin 2) (Fin 2) O) i j ∈ sourceKPDeepIdeal K P} := by
    ext g
    simpa only [Set.mem_iInter, Set.mem_ofPred_eq, SetLike.mem_coe] using
      sourceKPDeepIntegralGroup_mem_iff K P g
  rw [he]
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_iInter_of_finite
  intro j
  exact (sourceKPDeepIdeal_isOpen K P).preimage
    ((Units.continuous_val.matrix_elem i j).sub continuous_const)

lemma sourceKPDeepIntegralGroup_isCompact :
    IsCompact (sourceKPDeepIntegralGroup K P : Set (GL (Fin 2) O)) := by
  let : CompactSpace O := isCompact_iff_compactSpace.mp (sourceKPLocalIntegers_isCompact K P)
  let : CompactSpace (Matrix (Fin 2) (Fin 2) O) :=
    inferInstanceAs (CompactSpace (Fin 2 → Fin 2 → O))
  exact ((sourceKPDeepIntegralGroup K P).isClosed_of_isOpen
    (sourceKPDeepIntegralGroup_isOpen K P)).isCompact

lemma sourceKPDeepLocalBase_continuous : Continuous (sourceKPDeepLocalBase K P) :=
  (sourceKPIntegralMatrixMap_continuous K P).comp continuous_subtype_val

lemma sourceKPDeepLocalBase_isOpenEmbedding : IsOpenEmbedding (sourceKPDeepLocalBase K P) :=
  (sourceKPIntegralMatrixMap_isOpenEmbedding K P).comp
    (sourceKPDeepIntegralGroup_isOpen K P).isOpenEmbedding_subtypeVal

lemma sourceKPDeepLocalBase_range_isOpen : IsOpen (Set.range (sourceKPDeepLocalBase K P)) :=
  (sourceKPDeepLocalBase_isOpenEmbedding K P).isOpen_range

lemma sourceKPDeepLocalBase_range_isCompact : IsCompact (Set.range (sourceKPDeepLocalBase K P)) := by
  let : CompactSpace (sourceKPDeepIntegralGroup K P) :=
    isCompact_iff_compactSpace.mp (sourceKPDeepIntegralGroup_isCompact K P)
  exact isCompact_range (sourceKPDeepLocalBase_continuous K P)

end
end ArtinMatthews
