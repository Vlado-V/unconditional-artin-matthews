module

public import ArtinMatthews.SourceKPTranslateGramRepresentativeAE
public import ArtinMatthews.SourceKPTranslateGramGenuine
public import Mathlib.MeasureTheory.Measure.Regular


set_option backward.privateInPublic true
@[expose] public section

/-! The literal coset trace agrees with the actual Gram operator almost
everywhere on the compact quotient itself. -/
namespace ArtinMatthews
open NumberField Matrix MeasureTheory Filter Set
open scoped NumberField MatrixGroups AdeleRing BigOperators ENNReal
noncomputable section

private theorem ae_map_of_ae_comp_regular
    {X Y : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [T2Space Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure X) [SigmaFinite μ] [Measure.InnerRegularCompactLTTop μ]
    (q : X → Y) (hq : Continuous q) {p : Y → Prop}
    (hp : ∀ᵐ x ∂μ, p (q x)) : ∀ᵐ y ∂Measure.map q μ, p y := by
  obtain ⟨N,hN,hNm,hNz⟩ := exists_measurable_superset_of_null (ae_iff.mp hp)
  let S (m : ℕ) := Nᶜ ∩ spanningSets μ m
  have hS (m : ℕ) : MeasurableSet (S m) := hNm.compl.inter (measurableSet_spanningSets μ m)
  have hSfin (m : ℕ) : μ (S m) ≠ ∞ :=
    ((measure_mono inter_subset_right).trans_lt (measure_spanningSets_lt_top μ m)).ne
  have happrox (m n : ℕ) : ∃ C, C ⊆ S m ∧ IsCompact C ∧ μ (S m \ C) < (n : ℝ≥0∞)⁻¹ :=
    (hS m).exists_isCompact_sdiff_lt (hSfin m) (ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _))
  choose C hCsub hCcomp hCsmall using happrox
  let V : Set X := ⋃ m : ℕ, ⋃ n : ℕ, C m n
  have hCV (m n : ℕ) : C m n ⊆ V :=
    (subset_iUnion (C m) n).trans (subset_iUnion (fun m => ⋃ n, C m n) m)
  have hnull (m : ℕ) : μ (S m \ V) = 0 := by
    by_contra hne
    obtain ⟨n,hn⟩ := exists_nat_gt ((μ (S m \ V))⁻¹).toNNReal
    have hn' : (μ (S m \ V))⁻¹ < (n : ℝ≥0∞) := by
      rw [← ENNReal.coe_toNNReal (ENNReal.inv_ne_top.mpr hne)]
      exact_mod_cast hn
    have hlt : (n : ℝ≥0∞)⁻¹ < μ (S m \ V) := by
      simpa only [inv_inv] using (ENNReal.inv_lt_inv.mpr hn')
    have hm : μ (S m \ V) ≤ μ (S m \ C m n) :=
      measure_mono (fun _ hx => ⟨hx.1, fun h => hx.2 (hCV m n h)⟩)
    exact (not_lt_of_ge hm) ((hCsmall m n).trans hlt)
  have hV : μ Vᶜ = 0 := by
    apply measure_mono_null _ (measure_union_null hNz (measure_iUnion_null hnull))
    intro x hx
    by_cases hxn : x ∈ N
    · exact Or.inl hxn
    · have hxu : x ∈ ⋃ m, spanningSets μ m := by rw [iUnion_spanningSets]; trivial
      obtain ⟨m,hm⟩ := mem_iUnion.mp hxu
      exact Or.inr (mem_iUnion.mpr ⟨m,⟨⟨hxn,hm⟩,hx⟩⟩)
  let U : Set Y := ⋃ m : ℕ, ⋃ n : ℕ, q '' C m n
  have hU : MeasurableSet U :=
    MeasurableSet.iUnion fun m => MeasurableSet.iUnion fun n => ((hCcomp m n).image hq).measurableSet
  have hqU : q ⁻¹' Uᶜ ⊆ Vᶜ := by
    intro x hx hVx
    obtain ⟨m,hm⟩ := mem_iUnion.mp hVx
    obtain ⟨n,hn⟩ := mem_iUnion.mp hm
    exact hx (mem_iUnion.mpr ⟨m,mem_iUnion.mpr ⟨n,x,hn,rfl⟩⟩)
  have hUgood (y : Y) (hy : y ∈ U) : p y := by
    obtain ⟨m,hm⟩ := mem_iUnion.mp hy
    obtain ⟨n,x,hx,rfl⟩ := mem_iUnion.mp hm
    by_contra hx'
    exact (hCsub m n hx).1 (hN hx')
  have hbad : {y | ¬p y} ⊆ Uᶜ := by
    intro y hy h
    exact (show ¬p y from hy) (hUgood y h)
  refine ae_iff.mpr (measure_mono_null hbad ?_)
  rw [Measure.map_apply hq.measurable hU.compl]
  exact measure_mono_null hqU hV

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "F" => SourceKPFiniteLevelFiber K hζ
local notation "X" => SourceKPFiniteLevelSpace K hζ
local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "q" => sourceKPFiniteLevelToCompact K hζ
local notation "ν" => sourceKPFiniteRepresentativeHaar K hζ
local notation "μY" => sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)
local notation "E" => sourceKPTranslateBaseDomain K hζ

theorem sourceKPFiniteLevelToCompact_ae_of_comp {p : Y → Prop}
    (hp : ∀ᵐ x ∂ν, p (q x)) : ∀ᵐ y ∂μY, p y := by
  letI : SecondCountableTopology F := DiscreteTopology.secondCountableTopology_of_countable
  letI : BorelSpace X := inferInstanceAs (BorelSpace (PGL(2, InfiniteAdeleRing K) × F))
  letI : SigmaCompactSpace X := inferInstance
  letI : TopologicalSpace.PseudoMetrizableSpace X := inferInstance
  rw [← sourceKPTranslateBaseHaar_map]
  exact ae_map_of_ae_comp_regular ((ν).restrict E) q
    (sourceKPFiniteLevelToCompact_isOpenQuotientMap K hζ).continuous (ae_restrict_of_ae hp)

variable (T : Finset (SourceKPFiniteAdeleProjective K hζ))
include T

local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "D" => sourceKPFiniteLevelConjugate K hζ
local notation "J" => sourceKPFiniteTranslateLevel K hζ T
local notation "FJ" => SourceKPTranslateFiniteLevelFiber K hζ T
local notation "YJ" => SourceKPTranslateAutomorphicCompactLevel K hζ T
local notation "qJ" => sourceKPTranslateRepresentativeToCompact K hζ T
local notation "νJ" => sourceKPTranslateRepresentativeHaar K hζ T
local notation "μJ" => sourceKPTranslateCompactHaar K hζ T
local notation "LY" => Lp ℂ 2 μY
local notation "H" => SourceKPGenuineAutomorphicL2 K hζ
local notation "φ[" t ", " ht "]" => sourceKPFiniteRightTranslateMap K hζ T t ht
local notation "π[" t ", " ht "]" => sourceKPTranslateAutomorphicCompactMap K hζ T t ht
local notation "L[" t ", " ht ", " b "]" => {c : FJ // φ[t, ht] c = b}

theorem sourceKPTranslateCompactPullbackL2_representative_ae (u : Gf) (hu : J ≤ D u)
    (g : LY) : ∀ᵐ x ∂ν, ∀ c : FJ,
      sourceKPTranslateCompactPullbackL2 K hζ T u hu g (qJ (x.1,c)) =
        g (q (x.1,φ[u, hu] c)) := by
  have hP := sourceKPTranslateCompactPullbackL2_coe K hζ T u hu g
  have h := (sourceKPTranslateRepresentativeToCompact_full_quasiMeasurePreserving K hζ T).ae hP
  have h' := sourceKPTranslateRepresentative_ae_forall_coset K hζ T _ h
  filter_upwards [h'] with x hx
  intro c
  have hc := hx c
  change sourceKPTranslateCompactPullbackL2 K hζ T u hu g (qJ (x.1,c)) =
    g (π[u, hu] (qJ (x.1,c))) at hc
  have he := congrFun (sourceKPTranslateCompactMap_comp_representative K hζ T u hu) (x.1,c)
  change π[u, hu] (qJ (x.1,c)) = q (x.1,φ[u, hu] c) at he
  exact hc.trans (congrArg g he)

theorem sourceKPTranslateGenuineGramL2_representative_ae (t : Gf) (ht : J ≤ D t)
    (u : Gf) (hu : J ≤ D u) (g : H) :
    (fun x : X => (sourceKPTranslateGenuineGramL2 K hζ T t ht u hu g).val (q x)) =ᵐ[ν]
      fun x => ∑ c : L[t, ht, x.2], g.val (q (x.1,φ[u, hu] c.val)) := by
  rw [sourceKPTranslateGenuineGramL2_val]
  exact sourceKPTranslateScalarGramL2_representative_ae K hζ T t ht u hu g.val

theorem sourceKPTranslateGenuineGramL2_representative_pullback_ae (t : Gf) (ht : J ≤ D t)
    (u : Gf) (hu : J ≤ D u) (g : H) :
    (fun x : X => (sourceKPTranslateGenuineGramL2 K hζ T t ht u hu g).val (q x)) =ᵐ[ν]
      fun x => ∑ c : L[t, ht, x.2], sourceKPTranslateGenuinePullbackL2 K hζ T u hu g (qJ (x.1,c.val)) := by
  filter_upwards [sourceKPTranslateGenuineGramL2_representative_ae K hζ T t ht u hu g,
    sourceKPTranslateCompactPullbackL2_representative_ae K hζ T u hu g.val] with x h1 h2
  change (sourceKPTranslateGenuineGramL2 K hζ T t ht u hu g).val (q x) =
    ∑ c : L[t, ht, x.2], sourceKPTranslateGenuinePullbackL2 K hζ T u hu g (qJ (x.1,c.val))
  rw [h1]
  exact Finset.sum_congr rfl (fun c _ => (h2 c.val).symm)

theorem sourceKPTranslateScalarGramL2_trace_ae (t : Gf) (ht : J ≤ D t)
    (u : Gf) (hu : J ≤ D u) (g : LY) :
    (sourceKPTranslateScalarGramL2 K hζ T t ht u hu g : Y → ℂ) =ᵐ[μY]
      sourceKPTranslateCompactTrace K hζ T t ht (g ∘ π[u, hu]) := by
  apply sourceKPFiniteLevelToCompact_ae_of_comp K hζ
  filter_upwards [sourceKPTranslateScalarGramL2_representative_ae K hζ T t ht u hu g] with x hx
  change sourceKPTranslateScalarGramL2 K hζ T t ht u hu g (q x) =
    sourceKPTranslateCompactTrace K hζ T t ht (g ∘ π[u, hu]) (q x)
  let p := sourceKPArchSymmetricHomeomorph K hζ (QuotientGroup.mk x.1)
  have he (b : F) : q (x.1,b) = sourceKPUpperToCompact K hζ b p :=
    (sourceKPUpperToCompact_mk K hζ b x.1).symm
  rw [hx, show q x = sourceKPUpperToCompact K hζ x.2 p from he x.2,
    sourceKPTranslateCompactTrace_upper]
  simp only [Function.comp_apply, sourceKPTranslateAutomorphicCompactMap_upperMk, he]

theorem sourceKPTranslateGenuineGramL2_trace_ae (t : Gf) (ht : J ≤ D t)
    (u : Gf) (hu : J ≤ D u) (g : H) :
    ((sourceKPTranslateGenuineGramL2 K hζ T t ht u hu g).val : Y → ℂ) =ᵐ[μY]
      sourceKPTranslateCompactTrace K hζ T t ht (g.val ∘ π[u, hu]) := by
  rw [sourceKPTranslateGenuineGramL2_val]
  exact sourceKPTranslateScalarGramL2_trace_ae K hζ T t ht u hu g.val

end
end ArtinMatthews
