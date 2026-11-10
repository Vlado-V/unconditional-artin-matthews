module

public import ArtinMatthews.SourceArchSelfDualMeasure
public import ArtinMatthews.StandardAdelicInfiniteNontrivial
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
public import OAI.RepresentationTheory.Weil.AdelicSplitting.FourierTransport
public import OAI.RepresentationTheory.Weil.AdelicSplitting.ScalarPlancherel


set_option backward.privateInPublic true
@[expose] public section

/-! The actual standard additive character and its prescribed self-dual
measure at every complex completion. -/
namespace ArtinMatthews.SourceArchJacquet

open MeasureTheory NumberField NumberField.InfinitePlace
open ArtinMatthews.VaryingKummerAnalytic
open OAI.RepresentationTheory.Weil
open OAI.RepresentationTheory.Weil.AdelicSplitting
open scoped Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F]

local instance archCompletionMeasurable (v : InfinitePlace F) : MeasurableSpace v.Completion :=
  borel v.Completion
local instance archCompletionBorel (v : InfinitePlace F) : BorelSpace v.Completion := ⟨rfl⟩
local instance archCompletionSecondCountable (v : InfinitePlace F) :
    SecondCountableTopology v.Completion := by
  rcases v.isReal_or_isComplex with hv | hv
  · exact (Completion.isometryEquivRealOfIsReal hv).toHomeomorph.isEmbedding.secondCountableTopology
  · exact (Completion.isometryEquivComplexOfIsComplex hv).toHomeomorph.isEmbedding.secondCountableTopology

def sourceArchCompletionEquiv (v : InfinitePlace F) (hv : IsComplex v) : v.Completion ≃+* ℂ :=
  Completion.ringEquivComplexOfIsComplex hv

theorem sourceArchCompletion_character (v : InfinitePlace F) (hv : IsComplex v) (x : v.Completion) :
    StandardAdelic.localInfiniteCharacter F v x =
      sourceArchTraceCharacter (sourceArchCompletionEquiv F v hv x) := by
  rw [StandardAdelic.localInfiniteCharacter_single]
  change Complex.exp ((StandardAdelic.archTrace F (Pi.single v x) : ℂ) *
    (2 * (Real.pi : ℂ) * Complex.I)) = _
  rw [StandardAdelic.archTrace_single_complex F v hv, sourceArchTraceCharacter_apply,
    Real.fourierChar_apply]
  congr 1
  simp only [sourceArchCompletionEquiv, Completion.ringEquivComplexOfIsComplex_apply]
  push_cast
  ring

theorem sourceArchCompletion_selfDualMeasure (v : InfinitePlace F) (hv : IsComplex v) :
    (Local.FunctionsMetaplectic.Construction.selfDualMeasure v.Completion
      (StandardAdelic.localInfiniteCharacter F v)).map (sourceArchCompletionEquiv F v hv) =
        sourceComplexTraceMeasure := by
  let e := sourceArchCompletionEquiv F v hv
  let ψ := StandardAdelic.localInfiniteCharacter F v
  have he : Continuous e := (Completion.isometryEquivComplexOfIsComplex hv).continuous
  have hi : Continuous e.symm := (Completion.isometryEquivComplexOfIsComplex hv).symm.continuous
  have hψ : ψ.compAddMonoidHom e.symm.toAddMonoidHom = sourceArchTraceCharacter := by
    ext z
    change StandardAdelic.localInfiniteCharacter F v (e.symm z) = sourceArchTraceCharacter z
    rw [sourceArchCompletion_character F v hv]
    exact congrArg sourceArchTraceCharacter (e.apply_symm_apply z)
  have hc : Continuous sourceArchTraceCharacter := by
    have hcont : Continuous (fun z : ℂ => (Real.fourierChar (2 * z.re) : ℂ)) := by fun_prop
    exact hcont.congr (fun z => (sourceArchTraceCharacter_apply z).symm)
  have hu : ∀ z, ‖sourceArchTraceCharacter z‖ = 1 := by
    intro z
    rw [sourceArchTraceCharacter_apply]
    exact Circle.norm_coe _
  have hn : ∃ z, sourceArchTraceCharacter z ≠ 1 := by
    obtain ⟨x, hx⟩ := StandardAdelic.localInfiniteCharacter_nontrivial F v
    exact ⟨e x, by rw [← sourceArchCompletion_character F v hv]; exact hx⟩
  have : (Local.FunctionsMetaplectic.Construction.selfDualMeasure ℂ
      sourceArchTraceCharacter).IsAddHaarMeasure := by
    rw [sourceArchTraceCharacter_selfDualMeasure]
    exact Measure.IsAddHaarMeasure.smul volume (by norm_num : (2 : ENNReal) ≠ 0)
      (by norm_num : (2 : ENNReal) ≠ ⊤)
  have h := FourierTransport.LocalAnalysis.selfDualMeasure_fieldTransport e he hi ψ
    (Local.FunctionsMetaplectic.Construction.selfDualMeasure ℂ sourceArchTraceCharacter)
    (by
      intro S hS
      rw [hψ]
      exact ScalarPlancherel.LocalAnalysis.complex_scalar_indicator_plancherel
        sourceArchTraceCharacter hc hu hn hS)
  rw [sourceArchTraceCharacter_selfDualMeasure] at h
  exact h

theorem sourceArchCompletion_integral (v : InfinitePlace F) (hv : IsComplex v) (f : ℂ → ℂ) :
    (∫ x : v.Completion, f (sourceArchCompletionEquiv F v hv x)
      ∂Local.FunctionsMetaplectic.Construction.selfDualMeasure v.Completion
        (StandardAdelic.localInfiniteCharacter F v)) =
      ∫ z : ℂ, f z ∂sourceComplexTraceMeasure := by
  let e := sourceArchCompletionEquiv F v hv
  have he : Continuous e := (Completion.isometryEquivComplexOfIsComplex hv).continuous
  have hm : MeasurePreserving e
      (Local.FunctionsMetaplectic.Construction.selfDualMeasure v.Completion
        (StandardAdelic.localInfiniteCharacter F v)) sourceComplexTraceMeasure :=
    ⟨he.measurable, sourceArchCompletion_selfDualMeasure F v hv⟩
  exact hm.integral_comp (Completion.isometryEquivComplexOfIsComplex hv).toHomeomorph.measurableEmbedding f

theorem sourceArchCompletion_integrable (v : InfinitePlace F) (hv : IsComplex v)
    (f : ℂ → ℂ) (hf : Integrable f sourceComplexTraceMeasure) :
    Integrable (fun x : v.Completion => f (sourceArchCompletionEquiv F v hv x))
      (Local.FunctionsMetaplectic.Construction.selfDualMeasure v.Completion
        (StandardAdelic.localInfiniteCharacter F v)) := by
  let e := sourceArchCompletionEquiv F v hv
  have he : Continuous e := (Completion.isometryEquivComplexOfIsComplex hv).continuous
  have hm : MeasurePreserving e
      (Local.FunctionsMetaplectic.Construction.selfDualMeasure v.Completion
        (StandardAdelic.localInfiniteCharacter F v)) sourceComplexTraceMeasure :=
    ⟨he.measurable, sourceArchCompletion_selfDualMeasure F v hv⟩
  exact hm.integrable_comp_of_integrable hf

end
end ArtinMatthews.SourceArchJacquet
