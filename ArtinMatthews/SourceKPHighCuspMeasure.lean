module

public import ArtinMatthews.SourceKPArchHaar
public import ArtinMatthews.SourceKPAutomorphicMeasure
public import ArtinMatthews.SourceKPHighCuspQuotient
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

/-! The actual automorphic measure restricted to the genuine high-cusp subtype. -/
namespace ArtinMatthews
open NumberField Matrix Topology MeasureTheory Set
open scoped NumberField MatrixGroups AdeleRing ENNReal
noncomputable section
variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPHighCuspAutomorphic_isOpen (T : ℝ) :
    IsOpen {x : SourceKPAutomorphicLevel K hζ | T < sourceKPAutomorphicOrbitHeight K hζ x} := by
  simpa only [Set.compl_ofPred, not_le] using
    (sourceKPAutomorphicOrbitHeight_sublevel_closed K hζ T).isOpen_compl

def sourceKPHighCuspMeasure (T : ℝ) : Measure (SourceKPHighCuspAutomorphic K hζ T) :=
  Measure.comap Subtype.val (sourceKPAutomorphicMeasure K hζ (sourceKPArchHaar K hζ))

theorem sourceKPHighCuspMeasure_apply (T : ℝ) (A : Set (SourceKPHighCuspAutomorphic K hζ T)) :
    sourceKPHighCuspMeasure K hζ T A =
      sourceKPAutomorphicMeasure K hζ (sourceKPArchHaar K hζ) (Subtype.val '' A) :=
  (MeasurableEmbedding.subtype_coe (sourceKPHighCuspAutomorphic_isOpen K hζ T).measurableSet).comap_apply _ A

theorem sourceKPHighCuspMeasure_map_val (T : ℝ) :
    Measure.map Subtype.val (sourceKPHighCuspMeasure K hζ T) =
      (sourceKPAutomorphicMeasure K hζ (sourceKPArchHaar K hζ)).restrict
        {x | T < sourceKPAutomorphicOrbitHeight K hζ x} :=
  map_comap_subtype_coe (sourceKPHighCuspAutomorphic_isOpen K hζ T).measurableSet
    (sourceKPAutomorphicMeasure K hζ (sourceKPArchHaar K hζ))

theorem sourceKPHighCusp_representative (T : ℝ) (q : SourceKPHighCuspAutomorphic K hζ T) :
    ∃ x : SourceKPHighCuspFinite K hζ T, sourceKPHighCuspProjection K hζ T x = q := by
  obtain ⟨x,hx⟩ := sourceKPHighCuspQuotientMap_surjective K hζ T q
  obtain ⟨x,rfl⟩ := Quotient.mk_surjective x
  exact ⟨x,hx⟩

end
end ArtinMatthews
