module

public import ArtinMatthews.SourceKPCuspUpperAction
public import ArtinMatthews.SourceAdelicTraceHaar
public import ArtinMatthews.SourceKPCuspRepresentativeHaar
public import ArtinMatthews.SourceKPHighCuspMeasure
public import ArtinMatthews.SemidirectQuotientShear
public import ArtinMatthews.SourceAdelicScalarHaar
public import ArtinMatthews.SourceKPCuspFundamentalSection
public import ArtinMatthews.SourceKPCuspRationalScale
public import ArtinMatthews.SourceKPCuspSectionMeasure
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

/-! Full high-cusp averaging against the original quotient measure, with
the literal trace-normalized unipotent fundamental domain. -/
namespace ArtinMatthews
open NumberField Matrix Topology MeasureTheory Set
open OAI.RepresentationTheory.Weil.AdelicSplitting
open scoped NumberField MatrixGroups AdeleRing ENNReal

noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local instance sourceKPCuspAverageAdelicMeasurable : MeasurableSpace 𝔸[K] := borel _
local instance sourceKPCuspAverageAdelicBorel : BorelSpace 𝔸[K] := ⟨rfl⟩
local instance sourceKPCuspAverageAdelicSecondCountable : SecondCountableTopology 𝔸[K] :=
  (CompactQuotient.Construction.adelicMixedHomeomorph K).secondCountableTopology
local instance sourceKPCuspAverageMultiplicativeMeasurable : MeasurableSpace (Multiplicative 𝔸[K]) :=
  inferInstanceAs (MeasurableSpace 𝔸[K])

theorem sourceKPCuspHighUpper_finite_mk (T : ℝ) (y : 𝔸[K])
    (x : SourceKPHighCuspFinite K hζ T) (q : SourceKPAdelicProjective K hζ)
    (hq : sourceKPFiniteLevelMk K hζ q = x.val) :
    (Multiplicative.ofAdd y • x).val =
      sourceKPFiniteLevelMk K hζ (sourceKPAdelicUpperLift K hζ y*q) := by
  rw [sourceKPCuspHighUpper_val, sourceKPFiniteLevelMk_mul, hq]

theorem sourceKPCuspHighUpper_projection_mk (T : ℝ) (y : 𝔸[K])
    (x : SourceKPHighCuspFinite K hζ T) (q : SourceKPAdelicProjective K hζ)
    (hq : sourceKPFiniteLevelMk K hζ q = x.val) :
    (sourceKPHighCuspProjection K hζ T (Multiplicative.ofAdd y • x)).val =
      sourceKPAutomorphicLevelMk K hζ (sourceKPAdelicUpperLift K hζ y*q) :=
  congrArg (Quotient.mk _) (sourceKPCuspHighUpper_finite_mk K hζ T y x q hq)

include hζ in
private theorem sourceKPCuspTraceAffine_preserving (b : sourceKPRationalBorel K)
    (r : Multiplicative K) :
    MeasurePreserving
      (fun y : Multiplicative 𝔸[K] =>
        sourceKPCuspRationalAddHom K r * sourceKPCuspAdelicScaleAut K b y)
      (sourceKPAdelicTraceProduct K) (sourceKPAdelicTraceProduct K) := by
  rw [sourceKPAdelicTraceProduct_eq_standard_of_primitiveRoot K hζ]
  let a := sourceKPRationalCuspScale K b
  change MeasurePreserving
    (fun y : 𝔸[K] => algebraMap K 𝔸[K] r.toAdd + algebraMap K 𝔸[K] (a : K) * y)
    (sourceKPAdelicStandardHaar K) (sourceKPAdelicStandardHaar K)
  exact (measurePreserving_add_left (sourceKPAdelicStandardHaar K) _).comp
    (sourceKPAdelicStandardHaar_principal_mul K a)

private theorem sourceKPCuspTraceDomain_unique (y : Multiplicative 𝔸[K]) :
    ∃! r : Multiplicative K,
      sourceKPCuspRationalAddHom K r * y ∈ sourceKPAdelicFundamentalDomain K := by
  obtain ⟨q,hq,hqu⟩ := sourceKPAdelicFundamentalDomain_unique K y.toAdd
  refine ⟨Multiplicative.ofAdd (-q), ?_, ?_⟩
  · change algebraMap K 𝔸[K] (-q) + y.toAdd ∈ sourceKPAdelicFundamentalDomain K
    simpa only [map_neg, sub_eq_add_neg, add_comm] using hq
  · intro r hr
    change algebraMap K 𝔸[K] r.toAdd + y.toAdd ∈ sourceKPAdelicFundamentalDomain K at hr
    have hq' : y.toAdd - algebraMap K 𝔸[K] (-r.toAdd) ∈ sourceKPAdelicFundamentalDomain K := by
      simpa only [map_neg, sub_neg_eq_add, add_comm] using hr
    have he := congrArg Neg.neg (hqu (-r.toAdd) hq')
    change r.toAdd = -q
    simpa only [neg_neg] using he

theorem sourceKPCuspHighUpper_preserving (T : ℝ) (y : Multiplicative 𝔸[K]) :
    MeasurePreserving (fun x : SourceKPHighCuspFinite K hζ T => y • x)
      (sourceKPHighRepresentativeHaar K hζ T) (sourceKPHighRepresentativeHaar K hζ T) :=
  sourceKPHighRepresentativeHaar_left K hζ T (sourceKPAdelicUpperLift K hζ y.toAdd)
    (sourceKPFiniteLevelHeight_left_upper K hζ y.toAdd) _
    (sourceKPCuspHighUpper_val K hζ T y.toAdd)

theorem sourceKPCuspHighRationalBorel_preserving (T : ℝ) (b : sourceKPRationalBorel K) :
    MeasurePreserving (fun x : SourceKPHighCuspFinite K hζ T => b • x)
      (sourceKPHighRepresentativeHaar K hζ T) (sourceKPHighRepresentativeHaar K hζ T) :=
  sourceKPHighRepresentativeHaar_left K hζ T (sourceKPAdelicProjectiveRationalLift K hζ b.val)
    (sourceKPFiniteLevelHeight_rationalBorel K hζ b.val b.property) _ (fun _ => rfl)

private theorem sourceKPCuspHighUpper_rational (T : ℝ) (r : Multiplicative K)
    (x : SourceKPHighCuspFinite K hζ T) :
    sourceKPRationalCuspUpper K r • x = sourceKPCuspRationalAddHom K r • x := by
  apply Subtype.ext
  change sourceKPAdelicProjectiveRationalLift K hζ (sourceKPRationalCuspUpper K r).val • x.val =
    sourceKPAdelicUpperLift K hζ (algebraMap K 𝔸[K] r.toAdd) • x.val
  rw [sourceKPRationalCuspUpper_lift]

private theorem sourceKPCuspHighUpper_covariance (T : ℝ) (b : sourceKPRationalBorel K)
    (y : Multiplicative 𝔸[K]) (x : SourceKPHighCuspFinite K hζ T) :
    b • (y • x) = sourceKPCuspAdelicScaleAut K b y • (b • x) := by
  apply Subtype.ext
  change sourceKPAdelicProjectiveRationalLift K hζ b.val •
      (sourceKPAdelicUpperLift K hζ y.toAdd • x.val) =
    sourceKPAdelicUpperLift K hζ (algebraMap K 𝔸[K] (sourceKPRationalCuspScale K b : K) * y.toAdd) •
      (sourceKPAdelicProjectiveRationalLift K hζ b.val • x.val)
  rw [← mul_smul, ← mul_smul, sourceKPRationalCuspScale_upper_covariance]

/-- Average an integrable high-cusp function in its actual adelic unipotent
coordinate. The outer integral retains every finite and archimedean
coordinate of a measurable exact section, with its original Haar measure. -/
theorem sourceKPCuspHighSection_average_integral (T : ℝ) (hT : 1 < T)
    (F : Set (SourceKPHighCuspFinite K hζ T)) (hF : MeasurableSet F)
    (hinj : Set.InjOn (sourceKPHighCuspProjection K hζ T) F)
    (hcover : sourceKPHighCuspProjection K hζ T '' F = Set.univ)
    (f : SourceKPHighCuspAutomorphic K hζ T → ℂ)
    (hfi : Integrable f (sourceKPHighCuspMeasure K hζ T)) :
    Integrable (fun p : 𝔸[K] × SourceKPHighCuspFinite K hζ T =>
      f (sourceKPHighCuspProjection K hζ T (Multiplicative.ofAdd p.1 • p.2)))
      (((sourceKPAdelicTraceProduct K).restrict (sourceKPAdelicFundamentalDomain K)).prod
        ((sourceKPHighRepresentativeHaar K hζ T).restrict F)) ∧
    (∫ q, f q ∂sourceKPHighCuspMeasure K hζ T) =
      ∫ x in F, (∫ y in sourceKPAdelicFundamentalDomain K,
        f (sourceKPHighCuspProjection K hζ T (Multiplicative.ofAdd y • x))
          ∂sourceKPAdelicTraceProduct K) ∂sourceKPHighRepresentativeHaar K hζ T := by
  let p := sourceKPHighCuspProjection K hζ T
  let ν : Measure (Multiplicative 𝔸[K]) := sourceKPAdelicTraceProduct K
  let μ := sourceKPHighRepresentativeHaar K hζ T
  let D : Set (Multiplicative 𝔸[K]) := sourceKPAdelicFundamentalDomain K
  let : Countable (PGL(2,K)) := sourceKPCuspRationalProjective_countable K
  let : Countable (Multiplicative K) := inferInstanceAs (Countable K)
  let : SFinite ν := by
    change SFinite (sourceKPAdelicTraceProduct K)
    rw [sourceKPAdelicTraceProduct_eq_standard_of_primitiveRoot K hζ]
    infer_instance
  have hm := sourceKPCuspHighSection_measurePreserving K hζ T F hF hinj hcover
  have hfF : IntegrableOn (f ∘ p) F μ := hm.integrable_comp_of_integrable hfi
  have hjoint : Measurable (fun z : Multiplicative 𝔸[K] × SourceKPHighCuspFinite K hζ T =>
      z.1 • z.2) :=
    (sourceKPCuspHighUpperAction_continuous K hζ T).measurable
  have hinv : Measurable (fun y : Multiplicative 𝔸[K] => y⁻¹) :=
    (continuous_neg : Continuous (fun y : 𝔸[K] => -y)).measurable
  have hmass : ν D = 1 := by
    change sourceKPAdelicTraceProduct K (sourceKPAdelicFundamentalDomain K) = 1
    rw [sourceKPAdelicTraceProduct_eq_standard_of_primitiveRoot K hζ,
      sourceKPAdelicStandardHaar_fundamentalDomain]
  have h := semidirectQuotient_average (sourceKPCuspRationalScaleAut K)
    (sourceKPCuspAdelicScaleAut K) (sourceKPCuspRationalAddHom K)
    (sourceKPCuspRationalAddHom_scale K) ν μ
    (sourceKPCuspTraceAffine_preserving K hζ)
    (sourceKPCuspHighRationalBorel_preserving K hζ T)
    (sourceKPCuspHighUpper_preserving K hζ T) hjoint hinv
    (sourceKPRationalCuspUpper K) (sourceKPCuspAdelicScaleAut_upper K)
    (sourceKPCuspHighUpper_rational K hζ T) (sourceKPCuspHighUpper_covariance K hζ T)
    D F (sourceKPAdelicFundamentalDomain_measurable K) hF (sourceKPCuspTraceDomain_unique K)
    (sourceKPCuspHighSection_unique K hζ T hT F hinj hcover) hmass (f ∘ p) hfF
    (fun b x => congrArg f (sourceKPCuspHighProjection_rational K hζ T b x))
  refine ⟨h.1,?_⟩
  have hmap : AEStronglyMeasurable f (Measure.map p (μ.restrict F)) :=
    hm.map_eq.symm ▸ hfi.aestronglyMeasurable
  have he := integral_map hm.measurable.aemeasurable hmap
  rw [hm.map_eq] at he
  exact he.trans h.2

/-- The same actual averaging identity for real masses and energies. -/
theorem sourceKPCuspHighSection_average_integral_real (T : ℝ) (hT : 1 < T)
    (F : Set (SourceKPHighCuspFinite K hζ T)) (hF : MeasurableSet F)
    (hinj : Set.InjOn (sourceKPHighCuspProjection K hζ T) F)
    (hcover : sourceKPHighCuspProjection K hζ T '' F = Set.univ)
    (f : SourceKPHighCuspAutomorphic K hζ T → ℝ)
    (hfi : Integrable f (sourceKPHighCuspMeasure K hζ T)) :
    Integrable (fun p : 𝔸[K] × SourceKPHighCuspFinite K hζ T =>
      f (sourceKPHighCuspProjection K hζ T (Multiplicative.ofAdd p.1 • p.2)))
      (((sourceKPAdelicTraceProduct K).restrict (sourceKPAdelicFundamentalDomain K)).prod
        ((sourceKPHighRepresentativeHaar K hζ T).restrict F)) ∧
    (∫ q, f q ∂sourceKPHighCuspMeasure K hζ T) =
      ∫ x in F, (∫ y in sourceKPAdelicFundamentalDomain K,
        f (sourceKPHighCuspProjection K hζ T (Multiplicative.ofAdd y • x))
          ∂sourceKPAdelicTraceProduct K) ∂sourceKPHighRepresentativeHaar K hζ T := by
  have hfC : Integrable (fun q => (f q : ℂ)) (sourceKPHighCuspMeasure K hζ T) :=
    Complex.ofRealCLM.integrable_comp hfi
  have h := sourceKPCuspHighSection_average_integral K hζ T hT F hF hinj hcover
    (fun q => (f q : ℂ)) hfC
  refine ⟨?_, Complex.ofReal_injective ?_⟩
  · simpa only [Function.comp_def, Complex.reCLM_apply, Complex.ofReal_re] using
      Complex.reCLM.integrable_comp h.1
  · simpa only [integral_complex_ofReal] using h.2

end
end ArtinMatthews
