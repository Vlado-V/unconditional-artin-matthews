module

public import ArtinMatthews.SourceKPCuspRepresentativeHaar
public import ArtinMatthews.CountableChartSection
public import ArtinMatthews.SourceKPArithmeticLocalQuotient
public import ArtinMatthews.SourceKPAutomorphicBorel
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

/-! A measurable exact set of high representatives, selected inside any
measurable covering set of the actual high cusp. -/
namespace ArtinMatthews
open NumberField Matrix Topology MeasureTheory Set
open scoped NumberField MatrixGroups AdeleRing ENNReal

noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPCuspHighProjection_continuous (T : ℝ) :
    Continuous (sourceKPHighCuspProjection K hζ T) :=
  (sourceKPHighCuspQuotientMap_continuous K hζ T).comp continuous_quotient_mk'

theorem sourceKPCuspHighProjection_isOpenMap (T : ℝ) :
    IsOpenMap (sourceKPHighCuspProjection K hζ T) :=
  (sourceKPHighCuspQuotientMap_isOpen K hζ T).comp isOpenMap_quotient_mk'_mul

theorem sourceKPCuspHighProjection_rational (T : ℝ)
    (b : sourceKPRationalBorel K) (x : SourceKPHighCuspFinite K hζ T) :
    sourceKPHighCuspProjection K hζ T (b • x) = sourceKPHighCuspProjection K hζ T x := by
  apply Subtype.ext
  apply Quotient.sound
  exact MulAction.mem_orbit_iff.mpr ⟨b.val,rfl⟩

theorem sourceKPCuspHighProjection_eq_iff (T : ℝ) (hT : 1 < T)
    (x y : SourceKPHighCuspFinite K hζ T) :
    sourceKPHighCuspProjection K hζ T y = sourceKPHighCuspProjection K hζ T x ↔
      ∃ b : sourceKPRationalBorel K, b • x = y := by
  constructor
  · intro h
    have he : (Quotient.mk _ y : SourceKPHighCuspBorelQuotient K hζ T) = Quotient.mk _ x :=
      sourceKPHighCuspQuotientMap_injective K hζ T hT h
    exact MulAction.mem_orbit_iff.mp (Quotient.exact he)
  · rintro ⟨b,rfl⟩
    exact sourceKPCuspHighProjection_rational K hζ T b x

theorem sourceKPCuspRationalArchMap_injective :
    Function.Injective (sourceKPRationalArchMap K hζ) := by
  apply (injective_iff_map_eq_one (sourceKPRationalArchMap K hζ)).2
  intro γ hγ
  obtain ⟨g,rfl⟩ := ProjGenLinGroup.mk_surjective γ
  let f := algebraMap K (InfiniteAdeleRing K)
  change ProjGenLinGroup.map f (ProjGenLinGroup.mk g) = 1 at hγ
  rw [ProjGenLinGroup.map_mk, ProjGenLinGroup.mk_eq_one] at hγ
  apply ProjGenLinGroup.mk_eq_one.mpr
  rw [Subgroup.mem_center_iff] at hγ ⊢
  intro a
  have hcomm := hγ (GeneralLinearGroup.map f a)
  have he : GeneralLinearGroup.map f (a*g) = GeneralLinearGroup.map f (g*a) := by
    rw [map_mul, map_mul]
    exact hcomm
  apply GeneralLinearGroup.ext
  intro i j
  exact f.injective (congrArg (fun m : GL (Fin 2) (InfiniteAdeleRing K) => m i j) he)

private theorem sourceKPCuspHighAction_free (T : ℝ)
    (x : SourceKPHighCuspFinite K hζ T) (b c : sourceKPRationalBorel K)
    (h : b • x = c • x) : b = c := by
  have h' := congrArg (fun y : SourceKPHighCuspFinite K hζ T => y.val.1) h
  change sourceKPRationalArchMap K hζ b.val * x.val.1 =
    sourceKPRationalArchMap K hζ c.val * x.val.1 at h'
  exact Subtype.ext (sourceKPCuspRationalArchMap_injective K hζ (mul_right_cancel h'))

theorem sourceKPCuspHighProjection_localChart (T : ℝ)
    (x : SourceKPHighCuspFinite K hζ T) :
    ∃ U : Set (SourceKPHighCuspFinite K hζ T),
      IsOpen U ∧ x ∈ U ∧ Set.InjOn (sourceKPHighCuspProjection K hζ T) U := by
  obtain ⟨e,he,heq⟩ := sourceKPArchComponentPoint_localChart K hζ x.val.2 x.val.1
  let U : Set (SourceKPHighCuspFinite K hζ T) :=
    Subtype.val ⁻¹' (e.source ×ˢ {x.val.2})
  refine ⟨U, (e.open_source.prod (isOpen_discrete _)).preimage continuous_subtype_val,
    ⟨he,rfl⟩, ?_⟩
  intro y hy z hz h
  change y.val.1 ∈ e.source ∧ y.val.2 = x.val.2 at hy
  change z.val.1 ∈ e.source ∧ z.val.2 = x.val.2 at hz
  have heyz := congrArg Subtype.val h
  change (Quotient.mk _ y.val : SourceKPAutomorphicLevel K hζ) = Quotient.mk _ z.val at heyz
  have hval (v : SourceKPHighCuspFinite K hζ T) (hv : v.val.2 = x.val.2) :
      (Quotient.mk _ v.val : SourceKPAutomorphicLevel K hζ) =
        sourceKPArchComponentPoint K hζ x.val.2 v.val.1 :=
    congrArg (Quotient.mk _) (Prod.ext rfl hv)
  rw [hval y hy.2, hval z hz.2, heq] at heyz
  exact Subtype.ext (Prod.ext (e.injOn hy.1 hz.1 heyz) (hy.2.trans hz.2.symm))

theorem sourceKPCuspHighProjection_exists_section (T : ℝ)
    (C : Set (SourceKPHighCuspFinite K hζ T)) (hC : MeasurableSet C)
    (hcover : sourceKPHighCuspProjection K hζ T '' C = Set.univ) :
    ∃ F : Set (SourceKPHighCuspFinite K hζ T),
      MeasurableSet F ∧ F ⊆ C ∧ Set.InjOn (sourceKPHighCuspProjection K hζ T) F ∧
        sourceKPHighCuspProjection K hζ T '' F = Set.univ := by
  classical
  let X := SourceKPHighCuspFinite K hζ T
  let : SecondCountableTopology (SourceKPFiniteLevelFiber K hζ) :=
    DiscreteTopology.secondCountableTopology_of_countable
  let : SecondCountableTopology (PGL(2, InfiniteAdeleRing K)) :=
    sourceKPArchMeasure_secondCountable K
  let : SecondCountableTopology (SourceKPFiniteLevelSpace K hζ) :=
    inferInstanceAs (SecondCountableTopology
      (PGL(2, InfiniteAdeleRing K) × SourceKPFiniteLevelFiber K hζ))
  let : SecondCountableTopology X := TopologicalSpace.Subtype.secondCountableTopology
    {x : SourceKPFiniteLevelSpace K hζ | T < sourceKPFiniteLevelHeight K hζ x}
  let p := sourceKPHighCuspProjection K hζ T
  have hp := sourceKPCuspHighProjection_continuous K hζ T
  have hpo := sourceKPCuspHighProjection_isOpenMap K hζ T
  choose U ho hm hi using sourceKPCuspHighProjection_localChart K hζ T
  obtain ⟨J,hJ,hJU⟩ := TopologicalSpace.countable_cover_nhds
    (fun x : X => (ho x).mem_nhds (hm x))
  let : Countable J := hJ.to_subtype
  let V (j : J) := C ∩ U j.val
  have hVm (j : J) : MeasurableSet (V j) := hC.inter (ho j.val).measurableSet
  have hVim (j : J) : MeasurableSet (p '' V j) := by
    let q := fun x : U j.val => p x.val
    have hq : IsOpenEmbedding q := IsOpenEmbedding.of_continuous_injective_isOpenMap
      (hp.comp continuous_subtype_val)
      (fun _ _ he => Subtype.ext (hi j.val (Subtype.property _) (Subtype.property _) he))
      (hpo.comp (ho j.val).isOpenMap_subtype_val)
    have he : p '' V j = q '' (Subtype.val ⁻¹' C) := by
      ext y
      constructor
      · rintro ⟨x,hx,rfl⟩
        exact ⟨⟨x,hx.2⟩,hx.1,rfl⟩
      · rintro ⟨x,hx,rfl⟩
        exact ⟨x.val,⟨hx,x.property⟩,rfl⟩
    rw [he]
    exact hq.measurableEmbedding.measurableSet_image.mpr (hC.preimage measurable_subtype_coe)
  have hVc (y : SourceKPHighCuspAutomorphic K hζ T) : ∃ j : J, y ∈ p '' V j := by
    have hy : y ∈ p '' C := by
      change y ∈ sourceKPHighCuspProjection K hζ T '' C
      rw [hcover]
      trivial
    obtain ⟨x,hx,rfl⟩ := hy
    have hxU : x ∈ ⋃ z ∈ J, U z := by rw [hJU]; trivial
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hxU
    obtain ⟨hjJ,hxj⟩ := Set.mem_iUnion.mp hj
    exact ⟨⟨j,hjJ⟩,x,⟨hx,hxj⟩,rfl⟩
  obtain ⟨F,hF,hsub,hInj,hEq⟩ := exists_measurable_chart_section p hp.measurable V hVm hVim
    (fun j => (hi j.val).mono Set.inter_subset_right) hVc
  exact ⟨F,hF,hsub.trans (Set.iUnion_subset fun _ => Set.inter_subset_left),hInj,hEq⟩

theorem sourceKPCuspHighSection_unique (T : ℝ) (hT : 1 < T)
    (F : Set (SourceKPHighCuspFinite K hζ T))
    (hinj : Set.InjOn (sourceKPHighCuspProjection K hζ T) F)
    (hcover : sourceKPHighCuspProjection K hζ T '' F = Set.univ) :
    ∀ x : SourceKPHighCuspFinite K hζ T, ∃! b : sourceKPRationalBorel K, b • x ∈ F := by
  intro x
  let p := sourceKPHighCuspProjection K hζ T
  have hx : p x ∈ p '' F := by rw [hcover]; trivial
  obtain ⟨y,hy,he⟩ := hx
  obtain ⟨b,hb⟩ := (sourceKPCuspHighProjection_eq_iff K hζ T hT x y).1 he
  have hbF : b • x ∈ F := by rwa [hb]
  refine ⟨b,hbF,?_⟩
  intro c hc
  apply sourceKPCuspHighAction_free K hζ T x
  apply hinj hc hbF
  rw [sourceKPCuspHighProjection_rational, sourceKPCuspHighProjection_rational]

end
end ArtinMatthews
