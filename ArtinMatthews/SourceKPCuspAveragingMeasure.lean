module

public import ArtinMatthews.SourceAdelicTraceHaar
public import ArtinMatthews.SourceKPCuspRepresentativeHaar
public import ArtinMatthews.SourceKPCuspUpperAction
public import ArtinMatthews.SourceKPHighCuspMeasure
public import ArtinMatthews.SourceKPArithmeticDiscreteness
public import ArtinMatthews.SourceKPAutomorphicSigmaFinite
public import ArtinMatthews.SourceKPCuspFundamentalSection
public import ArtinMatthews.SourceKPCuspTraceAverage
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

/-! The actual unipotent averaging map pushes the entire trace-times-section
measure to the high-cusp automorphic measure. -/
namespace ArtinMatthews
open NumberField Matrix Topology MeasureTheory Set
open OAI.RepresentationTheory.Weil.AdelicSplitting
open scoped NumberField MatrixGroups AdeleRing ENNReal

noncomputable section

private theorem measurePreserving_of_real_integrals
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {ρ : Measure X} {μ : Measure Y} [SigmaFinite μ] {p : X → Y}
    (hp : Measurable p)
    (h : ∀ f : Y → ℝ, Integrable f μ →
      Integrable (f ∘ p) ρ ∧ (∫ y, f y ∂μ) = ∫ x, f (p x) ∂ρ) :
    MeasurePreserving p ρ μ := by
  refine ⟨hp,?_⟩
  have hfin (V : Set Y) (hV : MeasurableSet V) (hμ : μ V < ∞) :
      Measure.map p ρ V = μ V := by
    let f : Y → ℝ := V.indicator (fun _ => 1)
    have hf : Integrable f μ := (integrable_indicator_iff hV).2 (integrableOn_const hμ.ne)
    have hpre : MeasurableSet (p ⁻¹' V) := hV.preimage hp
    have he : f ∘ p = (p ⁻¹' V).indicator (fun _ => (1 : ℝ)) := by
      funext x
      by_cases hx : p x ∈ V <;> simp [f,hx]
    obtain ⟨hfi,hint⟩ := h f hf
    change (∫ y, f y ∂μ) = ∫ x, (f ∘ p) x ∂ρ at hint
    rw [he] at hfi hint
    have hρ : ρ (p ⁻¹' V) < ∞ :=
      ((integrableOn_const_iff (C := (1 : ℝ))).mp
        ((integrable_indicator_iff hpre).mp hfi)).resolve_left (by simp)
    change (∫ y, V.indicator (fun _ => (1 : ℝ)) y ∂μ) =
      ∫ x, (p ⁻¹' V).indicator (fun _ => (1 : ℝ)) x ∂ρ at hint
    simp only [integral_indicator_const (1 : ℝ) hV,
      integral_indicator_const (1 : ℝ) hpre, smul_eq_mul, mul_one] at hint
    rw [Measure.map_apply hp hV]
    have heq := congrArg ENNReal.ofReal hint.symm
    simpa only [measureReal_def, ENNReal.ofReal_toReal hρ.ne, ENNReal.ofReal_toReal hμ.ne] using heq
  apply Measure.ext_of_iUnion_eq_univ (iUnion_spanningSets μ)
  intro n
  ext V hV
  rw [Measure.restrict_apply hV, Measure.restrict_apply hV]
  exact hfin _ (hV.inter (measurableSet_spanningSets μ n))
    ((measure_mono Set.inter_subset_right).trans_lt (measure_spanningSets_lt_top μ n))

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local instance sourceKPCuspAveragingAdelicMeasurable : MeasurableSpace 𝔸[K] := borel _
local instance sourceKPCuspAveragingAdelicBorel : BorelSpace 𝔸[K] := ⟨rfl⟩
local instance sourceKPCuspAveragingAdelicSecondCountable : SecondCountableTopology 𝔸[K] :=
  (CompactQuotient.Construction.adelicMixedHomeomorph K).secondCountableTopology

theorem sourceKPCuspHighSection_averaging_measurePreserving (T : ℝ) (hT : 1 < T)
    (F : Set (SourceKPHighCuspFinite K hζ T)) (hF : MeasurableSet F)
    (hinj : Set.InjOn (sourceKPHighCuspProjection K hζ T) F)
    (hcover : sourceKPHighCuspProjection K hζ T '' F = Set.univ) :
    MeasurePreserving (fun p : 𝔸[K] × SourceKPHighCuspFinite K hζ T =>
      sourceKPHighCuspProjection K hζ T (Multiplicative.ofAdd p.1 • p.2))
      (((sourceKPAdelicTraceProduct K).restrict (sourceKPAdelicFundamentalDomain K)).prod
        ((sourceKPHighRepresentativeHaar K hζ T).restrict F))
      (sourceKPHighCuspMeasure K hζ T) := by
  let p := fun z : 𝔸[K] × SourceKPHighCuspFinite K hζ T =>
    sourceKPHighCuspProjection K hζ T (Multiplicative.ofAdd z.1 • z.2)
  let ν := (sourceKPAdelicTraceProduct K).restrict (sourceKPAdelicFundamentalDomain K)
  let μ := (sourceKPHighRepresentativeHaar K hζ T).restrict F
  have hν : IsProbabilityMeasure ν := ⟨by
    change ((sourceKPAdelicTraceProduct K).restrict (sourceKPAdelicFundamentalDomain K)) Set.univ = 1
    rw [Measure.restrict_apply MeasurableSet.univ,Set.univ_inter]
    exact sourceKPAdelicTraceProduct_fundamentalDomain_of_primitiveRoot K hζ⟩
  let : SigmaFinite (sourceKPHighCuspMeasure K hζ T) := by
    have hv : Measurable (Subtype.val :
        SourceKPHighCuspAutomorphic K hζ T → SourceKPAutomorphicLevel K hζ) :=
      measurable_subtype_coe
    apply SigmaFinite.of_map _ hv.aemeasurable
    rw [sourceKPHighCuspMeasure_map_val K hζ T]
    infer_instance
  have hp : Measurable p :=
    ((sourceKPCuspHighProjection_continuous K hζ T).comp
      (sourceKPCuspHighUpperAction_continuous K hζ T)).measurable
  apply measurePreserving_of_real_integrals hp
  intro f hf
  obtain ⟨hi,he⟩ := sourceKPCuspHighSection_average_integral_real K hζ T hT F hF hinj hcover f hf
  refine ⟨hi,he.trans ?_⟩
  exact (integral_prod_symm (fun z => f (p z)) hi).symm

end
end ArtinMatthews
