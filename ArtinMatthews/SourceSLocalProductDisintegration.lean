module

public import ArtinMatthews.SourceSLocalSheetHaar
public import ArtinMatthews.SourceComplexPlaceUnitHaar
public import ArtinMatthews.SourceSLocalRadialHaar
public import ArtinMatthews.SourceSLocalWholeSplitMeasure
public import ArtinMatthews.SourceComplexUnitPolarHomeomorph
public import ArtinMatthews.SourceLogRadialShear
public import ArtinMatthews.SourceProductSwapMiddle
public import ArtinMatthews.SourceSLocalRadialHomeomorph
public import ArtinMatthews.SourceSLocalRadialSheet
public import ArtinMatthews.SourceSLocalSheetBorel
public import ArtinMatthews.SourceSLocalWholeProductBorel
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
public import Mathlib.MeasureTheory.Measure.RegularityCompacts
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
public import Mathlib.Topology.UniformSpace.Uniformizable


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourcePhysical
open NumberField NumberField.InfinitePlace IsDedekindDomain MeasureTheory
open scoped NumberField Classical ENNReal
noncomputable section

variable {K : Type} [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable {v : InfinitePlace K} (hv : IsComplex v)
variable [∀ w : InfinitePlace K, MeasurableSpace w.Completionˣ]
variable [∀ p : S, MeasurableSpace (p.val.adicCompletion K)ˣ]
variable [∀ w : InfinitePlace K, BorelSpace w.Completionˣ]

variable (μarch : ∀ w : InfinitePlace K, Measure w.Completionˣ)
variable (μf : ∀ p : S, Measure (p.val.adicCompletion K)ˣ)
variable [∀ w, SigmaFinite (μarch w)] [∀ p, SigmaFinite (μf p)]

local notation "Other" => SNormOneOtherUnits S v
local notation "X" => (Circle × Other) × Multiplicative ℝ
local notation "μo" => (sourceSheetOtherMeasure S v μarch μf)
local notation "μA" => (Measure.prod sourceCircleHaar (sourceSheetOtherMeasure S v μarch μf))
local notation "μX" => (Measure.prod (Measure.prod sourceCircleHaar
  (sourceSheetOtherMeasure S v μarch μf)) sourceRealLogHaar)
local notation "μAll" => (Measure.prod (Measure.pi μarch) (Measure.pi μf))

def sourceSLocalPolarPlace (p : Circle × Multiplicative ℝ) : v.Completionˣ :=
  (sourceComplexPlaceUnitsEquiv hv).symm (sourceComplexUnitPolarMulEquiv p)

def sourceSLocalPolarAssembly (p : X) : SWholeUnits K S :=
  (sourceSWholeSheetSplit S v).symm (sourceSLocalPolarPlace hv (p.1.1,p.2),p.1.2)

omit [NumberField K] in
theorem sourceSLocalPolarPlace_measurable : Measurable (sourceSLocalPolarPlace hv) :=
  (sourceComplexPlaceUnitsEquiv hv).symm.continuous.measurable.comp
    sourceComplexUnitPolarHomeomorph.continuous.measurable

theorem sourceSLocalPolarAssembly_measurePreserving
    (hchosen : μarch v = Measure.map (sourceSLocalPolarPlace hv)
      (sourceCircleHaar.prod sourceRealLogHaar)) :
    MeasurePreserving (sourceSLocalPolarAssembly S hv) μX μAll := by
  have : IsFiniteMeasure sourceCircleHaar :=
    ⟨by rw [sourceCircleHaar_univ]; exact ENNReal.ofReal_lt_top⟩
  have : SigmaFinite μo := by
    unfold sourceSheetOtherMeasure
    infer_instance
  have hp : MeasurePreserving (sourceSLocalPolarPlace hv)
      (sourceCircleHaar.prod sourceRealLogHaar) (μarch v) :=
    ⟨sourceSLocalPolarPlace_measurable hv, hchosen.symm⟩
  have hsplit := sourceSWholeSheetSplit_symm_measurePreserving S v μarch μf
  exact sourceProductAssembly_measurePreserving sourceCircleHaar μo sourceRealLogHaar
    (μarch v) μAll (sourceSLocalPolarPlace hv) (sourceSWholeSheetSplit S v).symm hp hsplit

variable [∀ p : S, BorelSpace (p.val.adicCompletion K)ˣ]

/-- Exact disintegration of the product of the literal local measures. The angular measure
has mass `2π`, and no scalar is lost by using the total logarithmic norm. -/
theorem sourceSLocalProductMeasure_eq_radial
    (hchosen : μarch v = Measure.map (sourceSLocalPolarPlace hv)
      (sourceCircleHaar.prod sourceRealLogHaar)) :
    μAll =
      sourceSLocalRadialHaar S hv (sourceSNormOneSheetMeasure S hv μA) := by
  have : IsFiniteMeasure sourceCircleHaar :=
    ⟨by rw [sourceCircleHaar_univ]; exact ENNReal.ofReal_lt_top⟩
  have : BorelSpace Other := sourceSheetOtherUnits_product_borel S v
  have : BorelSpace (SWholeUnits K S) := sourceSWholeUnits_product_borel S v
  have : SigmaFinite μo := by unfold sourceSheetOtherMeasure; infer_instance
  let R : X → SWholeUnits K S := fun p => sourceSLocalRadialSheet S hv p.1 p.2.toAdd
  let T : X → X := fun p =>
    (p.1, Multiplicative.ofAdd (p.2.toAdd + Real.log (sourceSheetOtherNorm S v p.1.2)))
  have hlog : Measurable (fun a : Circle × Other => Real.log (sourceSheetOtherNorm S v a.2)) :=
    Real.measurable_log.comp ((measurable_sourceSheetOtherNorm S v).comp measurable_snd)
  have ht : MeasurePreserving T μX μX :=
    sourceLogRadial_shear_measurePreserving μA _ hlog
  have hm : Measurable (sourceSNormOneFromSheet hv S) :=
    (continuous_sourceSNormOneFromSheet hv S).measurable
  have hr : Measurable (sourceSLocalRadialMulEquiv hv S :
      SNormOne K S × Multiplicative ℝ → SWholeUnits K S) :=
    (sourceSLocalRadialHomeomorph hv S).continuous.measurable
  have hR : Measurable R := hr.comp (hm.prodMap measurable_id)
  have hcomp : R ∘ T = sourceSLocalPolarAssembly S hv := by
    funext p
    exact sourceSLocalRadialSheet_shear S hv p.1 p.2.toAdd
  have hprod : (Measure.map (sourceSNormOneFromSheet hv S) μA).prod sourceRealLogHaar =
      Measure.map (Prod.map (sourceSNormOneFromSheet hv S) id) μX := by
    simpa only [Measure.map_id] using
      Measure.map_prod_map μA sourceRealLogHaar hm measurable_id
  calc
    μAll = Measure.map (sourceSLocalPolarAssembly S hv) μX :=
      (sourceSLocalPolarAssembly_measurePreserving S hv μarch μf hchosen).map_eq.symm
    _ = Measure.map R μX := by
      rw [← hcomp, ← Measure.map_map hR ht.measurable, ht.map_eq]
    _ = _ := by
      rw [sourceSLocalRadialHaar, sourceSNormOneSheetMeasure, hprod,
        Measure.map_map hr (hm.prodMap measurable_id)]
      rfl

end
end ArtinMatthews.SourcePhysical
