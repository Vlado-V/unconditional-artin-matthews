module

public import ArtinMatthews.SourceSLocalWholeSplitMeasure
public import ArtinMatthews.SourceSLocalSheetBorel
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

/-! Compatibility of the actual whole product Borel structure with
the product of the local measurable structures. -/

namespace ArtinMatthews.SourcePhysical
open NumberField NumberField.InfinitePlace IsDedekindDomain MeasureTheory Topology
open scoped NumberField Classical
noncomputable section

variable {K : Type} [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K))) (v : InfinitePlace K)
variable [∀ w : InfinitePlace K, MeasurableSpace w.Completionˣ]
variable [∀ p : S, MeasurableSpace (p.val.adicCompletion K)ˣ]

include v in
theorem sourceSWholeUnits_product_borel
    [∀ w : InfinitePlace K, BorelSpace w.Completionˣ]
    [∀ p : S, BorelSpace (p.val.adicCompletion K)ˣ] :
    BorelSpace (SWholeUnits K S) := by
  let : BorelSpace (SNormOneOtherUnits S v) := sourceSheetOtherUnits_product_borel S v
  let : PolishSpace (SNormOneOtherUnits S v) := sourceSheetOtherUnits_polish S v
  let e := sourceSWholeSheetSplitMeasurableEquiv S v
  have he : IsInducing e := (sourceSWholeSheetSplit S v).toHomeomorph.isInducing
  exact e.measurableEmbedding.borelSpace he

theorem sourceSheetOtherMeasure_isHaar
    (μarch : ∀ w : InfinitePlace K, Measure w.Completionˣ)
    (μf : ∀ p : S, Measure (p.val.adicCompletion K)ˣ)
    [∀ w : InfinitePlace K, MeasurableMul w.Completionˣ] [∀ p : S, MeasurableMul (p.val.adicCompletion K)ˣ]
    [∀ w, SigmaFinite (μarch w)] [∀ p, SigmaFinite (μf p)]
    [∀ w, (μarch w).IsHaarMeasure] [∀ p, (μf p).IsHaarMeasure] :
    (sourceSheetOtherMeasure S v μarch μf).IsHaarMeasure := by
  let μo := fun w : {w : InfinitePlace K // w ≠ v} => μarch w.val
  have : (Measure.pi μo).IsHaarMeasure := Measure.pi.isHaarMeasure _
  have : (Measure.pi μf).IsHaarMeasure := Measure.pi.isHaarMeasure _
  change ((Measure.pi μo).prod (Measure.pi μf)).IsHaarMeasure
  infer_instance

end
end ArtinMatthews.SourcePhysical
