module

public import ArtinMatthews.SourceFinitePlaceHaar
public import ArtinMatthews.SourceCoordinateIntertwinerProduct
public import ArtinMatthews.SourceFiniteWindowExhaustion
public import ArtinMatthews.SourceFiniteIntertwinerIntegrable
public import ArtinMatthews.SourceJacquetHaarDilation
public import ArtinMatthews.SourceKPAdelicCoordinateIntegrable
public import ArtinMatthews.StandardLocalBall
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

namespace ArtinMatthews

open NumberField IsDedekindDomain MeasureTheory SourcePhysical Filter
open scoped NumberField AdeleRing BigOperators Topology
noncomputable section

variable (K : Type) [Field K] [NumberField K]

local instance finiteFubiniAdelicMeasurable : MeasurableSpace 𝔸[K] := borel 𝔸[K]
local instance finiteFubiniAdelicBorel : BorelSpace 𝔸[K] := ⟨rfl⟩
local instance finiteFubiniFiniteMeasurable : MeasurableSpace 𝔸ᶠ[K] := borel 𝔸ᶠ[K]
local instance finiteFubiniFiniteBorel : BorelSpace 𝔸ᶠ[K] := ⟨rfl⟩
local instance finiteFubiniCompletionMeasurable (P : HeightOneSpectrum (𝓞 K)) : MeasurableSpace (P.adicCompletion K) := borel _
local instance finiteFubiniCompletionBorel (P : HeightOneSpectrum (𝓞 K)) : BorelSpace (P.adicCompletion K) := ⟨rfl⟩

theorem sourceKPFiniteStandardHaar_integral_place (P : HeightOneSpectrum (𝓞 K))
    (f : 𝔸ᶠ[K] → ℂ) (hf : Integrable f (sourceKPFiniteStandardHaar K)) :
    (∫ y, f y ∂sourceKPFiniteStandardHaar K) =
      ∫ r : sourceKPFinitePlaceRemainder K P,
        (∫ x : P.adicCompletion K, f (sourceKPFiniteAdditiveSingle K P x + r.val)
          ∂sourceJacquetHaar K P) ∂sourceKPFinitePlaceRemainderStandardHaar K P := by
  let : (sourceJacquetHaar K P).IsAddHaarMeasure := sourceJacquetHaar_isAddHaar K P
  let e := (sourceKPFinitePlaceSplit K P).toHomeomorph.toMeasurableEquiv
  have hmeasure : sourceKPFiniteStandardHaar K = Measure.map e.symm
      ((sourceJacquetHaar K P).prod (sourceKPFinitePlaceRemainderStandardHaar K P)) :=
    sourceKPFiniteStandardHaar_place_split K P
  have hi : Integrable (fun p => f (e.symm p))
      ((sourceJacquetHaar K P).prod (sourceKPFinitePlaceRemainderStandardHaar K P)) := by
    apply (integrable_map_equiv e.symm f).mp
    rw [← hmeasure]
    exact hf
  rw [hmeasure]
  change (∫ x, f x ∂Measure.map e.symm
    ((sourceJacquetHaar K P).prod (sourceKPFinitePlaceRemainderStandardHaar K P))) = _
  rw [integral_map_equiv]
  exact integral_prod_symm (fun p => f (e.symm p)) hi

variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPFiniteIntertwiner_place_fubini (P : HeightOneSpectrum (𝓞 K))
    {s : ℂ} (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2 * s.re + 1)
    (g : SourceKPFiniteAdeleProjective K hζ) :
    sourceKPFiniteIntertwiner K hζ s g =
      ∫ r : sourceKPFinitePlaceRemainder K P,
        (∫ x : P.adicCompletion K,
          sourceKPFiniteIntertwiningKernel K hζ s g
            (sourceKPFiniteAdditiveSingle K P x + r.val)
          ∂sourceJacquetHaar K P) ∂sourceKPFinitePlaceRemainderStandardHaar K P :=
  sourceKPFiniteStandardHaar_integral_place K P _
    (sourceKPFiniteIntertwiningKernel_integrable K hζ hs g)

theorem sourceKPFiniteIntertwiner_good_place_fubini (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ StandardAdelic.traceBadPlaces K)
    {s : ℂ} (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2 * s.re + 1)
    (g : SourceKPFiniteAdeleProjective K hζ) :
    sourceKPFiniteIntertwiner K hζ s g =
      ∫ r : sourceKPFinitePlaceRemainder K P,
        (∫ x : P.adicCompletion K,
          sourceKPFiniteIntertwiningKernel K hζ s g
            (sourceKPFiniteAdditiveSingle K P x + r.val)
          ∂sourceLocalSelfDual K P) ∂sourceKPFinitePlaceRemainderStandardHaar K P := by
  rw [← sourceJacquetHaar_eq_selfDual K P hP]
  exact sourceKPFiniteIntertwiner_place_fubini K hζ P hs g

theorem sourceKPFiniteCoordinateIntertwiningKernel_integrable
    {s : ℂ} (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2 * s.re + 1)
    (g : SourceKPAdelicProjective K hζ) (t : sourceKPAdelicCoveringTorus K hζ) :
    Integrable (sourceKPFiniteCoordinateIntertwiningKernel K hζ s g.2 t.val.2)
      (sourceKPFiniteStandardHaar K) := by
  have hd : sourceKPAdelicBorelModularHalf K hζ
      (sourceKPAdelicBorelTorusInclusion K hζ t) ≠ 0 := by
    change (sourceKPIdeleComplexNorm K (1 / 2 : ℂ)
      (sourceKPAdelicTorusIdele K hζ
        (sourceKPAdelicBorelTorusProjection K hζ
          (sourceKPAdelicBorelTorusInclusion K hζ t))) : ℂ) ≠ 0
    exact Units.ne_zero _
  have ha : sourceArchSphericalProduct K hζ s t.val.1 ≠ 0 := by
    unfold sourceArchSphericalProduct
    exact Finset.prod_ne_zero_iff.mpr (fun _ _ => sourceKPArchSphericalSection_ne_zero s _)
  let f := fun x =>
    (sourceKPAdelicBorelModularHalf K hζ
      (sourceKPAdelicBorelTorusInclusion K hζ t))⁻¹ *
      sourceArchSphericalProduct K hζ s t.val.1 *
      sourceKPArchIntertwiningKernel K hζ s g.1 x
  apply sourceKPTraceProduct_finite_integrable K hζ f
    (sourceKPFiniteCoordinateIntertwiningKernel K hζ s g.2 t.val.2)
  · intro x
    exact mul_ne_zero (mul_ne_zero (inv_ne_zero hd) ha)
      (sourceKPArchIntertwiningKernel_ne_zero K hζ s g.1 x)
  · let : (sourceKPAdelicTraceProduct K).IsAddHaarMeasure := by
      rw [sourceKPAdelicTraceProduct_eq_standard_of_primitiveRoot K hζ]
      infer_instance
    have hi := sourceKPAdelicCoordinateKernel_integrable K hζ
      (sourceKPAdelicTraceProduct K) hs g t
    exact hi.congr (Filter.Eventually.of_forall (fun y =>
      sourceKPAdelicCoordinateKernel_arch_finite K hζ s g t y))

theorem sourceKPFiniteCoordinateIntertwiner_place_fubini (P : HeightOneSpectrum (𝓞 K))
    {s : ℂ} (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2 * s.re + 1)
    (g : SourceKPAdelicProjective K hζ) (t : sourceKPAdelicCoveringTorus K hζ) :
    sourceKPFiniteCoordinateIntertwiner K hζ s g.2 t.val.2 =
      ∫ r : sourceKPFinitePlaceRemainder K P,
        (∫ x : P.adicCompletion K,
          sourceKPFiniteCoordinateIntertwiningKernel K hζ s g.2 t.val.2
            (sourceKPFiniteAdditiveSingle K P x + r.val)
          ∂sourceJacquetHaar K P) ∂sourceKPFinitePlaceRemainderStandardHaar K P :=
  sourceKPFiniteStandardHaar_integral_place K P _
    (sourceKPFiniteCoordinateIntertwiningKernel_integrable K hζ hs g t)

theorem sourceKPFiniteCoordinateIntertwiner_window_tendsto
    {s : ℂ} (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2 * s.re + 1)
    (g : SourceKPAdelicProjective K hζ) (t : sourceKPAdelicCoveringTorus K hζ) :
    Tendsto (fun S : Finset (HeightOneSpectrum (𝓞 K)) =>
      ∫ x in sourceKPFiniteWindow K S,
        sourceKPFiniteCoordinateIntertwiningKernel K hζ s g.2 t.val.2 x
        ∂sourceKPFiniteStandardHaar K) atTop
      (𝓝 (sourceKPFiniteCoordinateIntertwiner K hζ s g.2 t.val.2)) :=
  sourceKPFiniteWindow_integral_tendsto K _ _
    (sourceKPFiniteCoordinateIntertwiningKernel_integrable K hζ hs g t)

end
end ArtinMatthews
