module

public import ArtinMatthews.SourceAdelicStandardHaar
public import ArtinMatthews.SourceArchCompletedMeasure
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
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! At totally complex number fields the archimedean factor is the tensor
product of the prescribed completion-wise trace-self-dual measures. -/
namespace ArtinMatthews
open NumberField NumberField.InfinitePlace MeasureTheory SourceArchJacquet
open OAI.RepresentationTheory.Weil OAI.RepresentationTheory.Weil.AdelicSplitting
open scoped NumberField AdeleRing Topology Classical ENNReal
noncomputable section
variable (K : Type) [Field K] [NumberField K]

local instance sourceKPArchSelfDualCompletionMeasurable (v : InfinitePlace K) :
    MeasurableSpace v.Completion := borel _
local instance sourceKPArchSelfDualCompletionBorel (v : InfinitePlace K) :
    BorelSpace v.Completion := ⟨rfl⟩
local instance sourceKPArchSelfDualInfiniteMeasurable : MeasurableSpace (InfiniteAdeleRing K) :=
  inferInstanceAs (MeasurableSpace (∀ v : InfinitePlace K, v.Completion))
local instance sourceKPArchSelfDualInfiniteBorel : BorelSpace (InfiniteAdeleRing K) := by
  change BorelSpace (∀ v : InfinitePlace K, v.Completion)
  have (v : InfinitePlace K) : SecondCountableTopology v.Completion := by
    rcases v.isReal_or_isComplex with hv | hv
    · exact (Completion.isometryEquivRealOfIsReal hv).toHomeomorph.secondCountableTopology
    · exact (Completion.isometryEquivComplexOfIsComplex hv).toHomeomorph.secondCountableTopology
  infer_instance

variable (hc : ∀ v : InfinitePlace K, IsComplex v)

def sourceKPComplexPlaceEquiv : {v : InfinitePlace K // IsComplex v} ≃ InfinitePlace K where
  toFun := Subtype.val
  invFun := fun v => ⟨v, hc v⟩
  left_inv _ := rfl
  right_inv _ := rfl

def sourceKPMixedComplexMeasurableEquiv :
    mixedEmbedding.mixedSpace K ≃ᵐ (InfinitePlace K → ℂ) where
  toFun x v := x.2 ⟨v, hc v⟩
  invFun z := (fun v => False.elim ((not_isReal_iff_isComplex.mpr (hc v.1)) v.2),
    fun v => z v.1)
  left_inv x := by
    apply Prod.ext
    · funext v
      exact False.elim ((not_isReal_iff_isComplex.mpr (hc v.1)) v.2)
    · rfl
  right_inv _ := rfl
  measurable_toFun := by
    change Measurable (fun (x : mixedEmbedding.mixedSpace K) (v : InfinitePlace K) => x.2 ⟨v, hc v⟩)
    fun_prop
  measurable_invFun := by
    change Measurable (fun z : InfinitePlace K → ℂ =>
      ((fun v : {v : InfinitePlace K // IsReal v} =>
        False.elim ((not_isReal_iff_isComplex.mpr (hc v.1)) v.2)),
       fun v : {v : InfinitePlace K // IsComplex v} => z v.1))
    fun_prop

theorem sourceKPMixedComplexMeasurableEquiv_volume :
    (volume : Measure (mixedEmbedding.mixedSpace K)).map
      (sourceKPMixedComplexMeasurableEquiv K hc) = volume := by
  let : IsEmpty {v : InfinitePlace K // IsReal v} :=
    ⟨fun v => (not_isReal_iff_isComplex.mpr (hc v.1)) v.2⟩
  let : IsProbabilityMeasure (volume : Measure ({v : InfinitePlace K // IsReal v} → ℝ)) := by
    constructor
    change (Measure.pi fun _ : {v : InfinitePlace K // IsReal v} => (volume : Measure ℝ)) Set.univ = 1
    simp only [Measure.pi_univ, Finset.univ_eq_empty, Finset.prod_empty]
  have hs : MeasurePreserving Prod.snd
      (volume : Measure (mixedEmbedding.mixedSpace K))
      (volume : Measure ({v : InfinitePlace K // IsComplex v} → ℂ)) :=
    measurePreserving_snd
  exact ((volume_measurePreserving_piCongrLeft (fun _ : InfinitePlace K => ℂ)
    (sourceKPComplexPlaceEquiv K hc)).comp hs).map_eq

def sourceKPArchSelfDualProduct : Measure (InfiniteAdeleRing K) :=
  Measure.pi (fun v => Local.FunctionsMetaplectic.Construction.selfDualMeasure v.Completion
    (StandardAdelic.localInfiniteCharacter K v))

theorem sourceKPArchSelfDualProduct_complexCoordinates :
    (sourceKPArchSelfDualProduct K).map
      (fun a v => sourceArchCompletionEquiv K v (hc v) (a v)) =
      (2 : ℝ≥0∞) ^ Fintype.card (InfinitePlace K) •
        (volume : Measure (InfinitePlace K → ℂ)) := by
  let μ (v : InfinitePlace K) := Local.FunctionsMetaplectic.Construction.selfDualMeasure v.Completion
    (StandardAdelic.localInfiniteCharacter K v)
  have hmap (v : InfinitePlace K) :
      (μ v).map (sourceArchCompletionEquiv K v (hc v)) = (2 : ℝ≥0∞) • (volume : Measure ℂ) :=
    sourceArchCompletion_selfDualMeasure K v (hc v)
  let : ((2 : ℝ≥0∞) • (volume : Measure ℂ)).IsAddHaarMeasure :=
    Measure.IsAddHaarMeasure.smul _ (by norm_num) (by norm_num)
  let (v : InfinitePlace K) : SigmaFinite ((μ v).map (sourceArchCompletionEquiv K v (hc v))) := by
    rw [hmap v]
    infer_instance
  change (Measure.pi μ).map (fun (a : ∀ v : InfinitePlace K, v.Completion) v =>
    sourceArchCompletionEquiv K v (hc v) (a v)) = _
  rw [Measure.pi_map_pi (f := fun v => sourceArchCompletionEquiv K v (hc v)) (fun v =>
    (Completion.isometryEquivComplexOfIsComplex (hc v)).continuous.measurable.aemeasurable)]
  simp_rw [hmap]
  apply Measure.pi_eq
  intro s hs
  simp only [Measure.smul_apply, smul_eq_mul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ]
  change (2 : ℝ≥0∞) ^ Fintype.card (InfinitePlace K) *
    (Measure.pi fun _ : InfinitePlace K => (volume : Measure ℂ)) (Set.univ.pi s) = _
  rw [Measure.pi_pi]

include hc in
theorem sourceKPArchSelfDualProduct_mixedSpace :
    (sourceKPArchSelfDualProduct K).map (InfiniteAdeleRing.ringEquiv_mixedSpace K) =
      sourceKPArchStandardHaar K := by
  let e := sourceKPMixedComplexMeasurableEquiv K hc
  apply e.measurableEmbedding.map_injective
  have hm : Measurable (InfiniteAdeleRing.ringEquiv_mixedSpace K) :=
    (ArchimedeanAdeles.Construction.infiniteAdeleMixedHomeomorph K).continuous.measurable
  rw [Measure.map_map e.measurable hm]
  have he : e ∘ InfiniteAdeleRing.ringEquiv_mixedSpace K =
      (fun a v => sourceArchCompletionEquiv K v (hc v) (a v)) := by
    funext a v
    rfl
  rw [he, sourceKPArchSelfDualProduct_complexCoordinates,
    sourceKPArchStandardHaar, Measure.map_smul,
    sourceKPMixedComplexMeasurableEquiv_volume K hc]
  · congr 1
    exact congrArg (fun n => (2 : ℝ≥0∞) ^ n) (Fintype.card_congr (sourceKPComplexPlaceEquiv K hc)).symm
  · exact e.measurable.aemeasurable

end
end ArtinMatthews
