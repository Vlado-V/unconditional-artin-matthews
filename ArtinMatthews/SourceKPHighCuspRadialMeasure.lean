module

public import ArtinMatthews.SourceKPHighCuspMeasure
public import ArtinMatthews.SourceKPRadialHighFlow
public import ArtinMatthews.MeasureLocallyEqual
public import ArtinMatthews.SourceKPArchRadialHaar
public import ArtinMatthews.SourceKPArithmeticLocalQuotient
public import ArtinMatthews.SourceKPAutomorphicComponentTopology
public import ArtinMatthews.SourceKPHighCuspRadialChartMeasure
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

/-! Exact full automorphic measure transport under the genuine high-cusp radial flow. -/
namespace ArtinMatthews
open NumberField Matrix Topology MeasureTheory Set
open scoped NumberField MatrixGroups AdeleRing ENNReal
noncomputable section
variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPHighCuspRadialHomeomorph_map_measure (t T : ℝ) (hT : 1 < T)
    (htT : 1 < sourceKPRadialHeightScale K t*T) :
    Measure.map (sourceKPHighCuspRadialHomeomorph K hζ t T hT htT)
      (sourceKPHighCuspMeasure K hζ T) =
      ENNReal.ofReal (sourceKPRadialHeightScale K t) •
        sourceKPHighCuspMeasure K hζ (sourceKPRadialHeightScale K t*T) := by
  let : SecondCountableTopology (SourceKPAutomorphicLevel K hζ) :=
    sourceKPAutomorphicLevel_secondCountable K hζ
  let : SecondCountableTopology
      (SourceKPHighCuspAutomorphic K hζ (sourceKPRadialHeightScale K t*T)) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  let e := sourceKPHighCuspRadialHomeomorph K hζ t T hT htT
  let F := sourceKPArchRadialHomeomorph K hζ t
  change Measure.map e (sourceKPHighCuspMeasure K hζ T) = _
  apply measure_eq_of_locally_restrict
  intro y
  obtain ⟨x,hx⟩ := sourceKPHighCusp_representative K hζ T (e.symm y)
  let g := x.val.1
  let b := x.val.2
  let j := sourceKPArchComponentPoint K hζ b
  obtain ⟨c,hgc,hjc⟩ := sourceKPArchComponentPoint_localChart K hζ b g
  let U := c.source ∩ {a | T < sourceKPFiniteLevelHeight K hζ (a,b)}
  have harg : Continuous (fun a : PGL(2, InfiniteAdeleRing K) => (a,b)) :=
    continuous_id.prodMk continuous_const
  have hheight : Continuous (fun a : PGL(2, InfiniteAdeleRing K) =>
      sourceKPFiniteLevelHeight K hζ (a,b)) := by
    have h := (sourceKPFiniteLevelHeight_continuous K hζ).comp harg
    simpa only [Function.comp_def] using h
  have hU : IsOpen U := c.open_source.inter (isOpen_lt continuous_const hheight)
  have hgU : g ∈ U := ⟨hgc,x.property⟩
  have hhigh : ∀ a ∈ U, T < sourceKPFiniteLevelHeight K hζ (a,b) := fun _ ha => ha.2
  have hinj : Set.InjOn j U := by
    intro a ha a' ha' heq
    apply c.injOn ha.1 ha'.1
    change sourceKPArchComponentPoint K hζ b a = sourceKPArchComponentPoint K hζ b a' at heq
    simpa only [hjc] using heq
  let V : Set (SourceKPHighCuspAutomorphic K hζ (sourceKPRadialHeightScale K t*T)) := Subtype.val ⁻¹' ((fun a => j (F a)) '' U)
  have hV : IsOpen V := by
    have hopen := sourceKPArchComponentPoint_isOpenMap K hζ b (F '' U) (F.isOpenMap U hU)
    rw [Set.image_image] at hopen
    exact hopen.preimage continuous_subtype_val
  have hyV : y ∈ V := by
    have hexy : e (sourceKPHighCuspProjection K hζ T x) = y := by
      rw [hx, Homeomorph.apply_symm_apply]
    have hrep := congrArg Subtype.val
      (sourceKPHighCuspRadialHomeomorph_rep K hζ t T hT htT x)
    have hgy : j (F g) = y.val := hrep.symm.trans (congrArg Subtype.val hexy)
    exact ⟨g,hgU,hgy⟩
  refine ⟨V,hV,hyV,?_⟩
  ext A hA
  rw [Measure.restrict_apply hA, Measure.map_apply e.measurable (hA.inter hV.measurableSet),
    Measure.restrict_apply hA, Measure.smul_apply]
  apply sourceKPHighCuspRadial_measure_chart K hζ t T hT htT b U hU.measurableSet hhigh hinj
    (A ∩ V) (hA.inter hV.measurableSet)
  rintro _ ⟨q,hq,rfl⟩
  exact hq.2

theorem sourceKPHighCuspRadialValue_map_measure (t T : ℝ) (hT : 1 < T)
    (htT : 1 < sourceKPRadialHeightScale K t*T) :
    Measure.map (sourceKPHighCuspRadialValue K hζ t T hT)
      (sourceKPHighCuspMeasure K hζ T) =
      ENNReal.ofReal (sourceKPRadialHeightScale K t) •
        (sourceKPAutomorphicMeasure K hζ (sourceKPArchHaar K hζ)).restrict
          {x | sourceKPRadialHeightScale K t*T < sourceKPAutomorphicOrbitHeight K hζ x} := by
  have he : sourceKPHighCuspRadialValue K hζ t T hT =
      Subtype.val ∘ sourceKPHighCuspRadialHomeomorph K hζ t T hT htT := by
    funext q
    exact (sourceKPHighCuspRadialHomeomorph_value K hζ t T hT htT q).symm
  rw [he, ← Measure.map_map measurable_subtype_coe
    (sourceKPHighCuspRadialHomeomorph K hζ t T hT htT).measurable,
    sourceKPHighCuspRadialHomeomorph_map_measure, Measure.map_smul _ measurable_subtype_coe.aemeasurable,
    sourceKPHighCuspMeasure_map_val]

theorem sourceKPHighCuspRadialHomeomorph_image_measure (t T : ℝ) (hT : 1 < T)
    (htT : 1 < sourceKPRadialHeightScale K t*T)
    (A : Set (SourceKPHighCuspAutomorphic K hζ T)) (hA : MeasurableSet A) :
    sourceKPHighCuspMeasure K hζ (sourceKPRadialHeightScale K t*T)
      (sourceKPHighCuspRadialHomeomorph K hζ t T hT htT '' A) =
      ENNReal.ofReal (sourceKPRadialHeightScale K (-t)) * sourceKPHighCuspMeasure K hζ T A := by
  let e := sourceKPHighCuspRadialHomeomorph K hζ t T hT htT
  have himage : MeasurableSet (e '' A) := e.measurableEmbedding.measurableSet_image.mpr hA
  have hm := congrArg (fun μ => μ (e '' A))
    (sourceKPHighCuspRadialHomeomorph_map_measure K hζ t T hT htT)
  change (Measure.map e (sourceKPHighCuspMeasure K hζ T)) (e '' A) =
    (ENNReal.ofReal (sourceKPRadialHeightScale K t) •
      sourceKPHighCuspMeasure K hζ (sourceKPRadialHeightScale K t*T)) (e '' A) at hm
  rw [Measure.map_apply e.measurable himage, Set.preimage_image_eq _ e.injective,
    Measure.smul_apply, smul_eq_mul] at hm
  have hc : ENNReal.ofReal (sourceKPRadialHeightScale K (-t)) *
      ENNReal.ofReal (sourceKPRadialHeightScale K t) = 1 := by
    rw [← ENNReal.ofReal_mul (sourceKPRadialHeightScale_pos K (-t)).le,
      sourceKPRadialHeightScale_neg_mul, ENNReal.ofReal_one]
  calc
    _ = (ENNReal.ofReal (sourceKPRadialHeightScale K (-t)) *
        ENNReal.ofReal (sourceKPRadialHeightScale K t)) *
        sourceKPHighCuspMeasure K hζ (sourceKPRadialHeightScale K t*T) (e '' A) := by rw [hc,one_mul]
    _ = _ := by rw [mul_assoc, ← hm]

end
end ArtinMatthews
