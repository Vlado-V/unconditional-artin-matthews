module

public import ArtinMatthews.SourceKPCuspArchRepresentative
public import ArtinMatthews.SourceKPCuspNativeTraceSlice
public import ArtinMatthews.SourceKPCuspProductMeasure
public import ArtinMatthews.SourceKPCuspHeightAE
public import ArtinMatthews.SourceKPCuspLevelTopology
public import ArtinMatthews.SourceKPCuspNativeTraceL2
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

/-! The full archimedean representative has the same normalized adelic
constant term as its principal torus slice. -/
namespace ArtinMatthews
open NumberField Module.Free MeasureTheory SourceHyperbolicGreen StandardAdelic UnitAddTorus
open scoped NumberField AdeleRing MatrixGroups ENNReal NNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
local notation "I" => ChooseBasisIndex ℤ (𝓞 K)
local notation "V" => InfinitePlace K
local notation "G" => PGL(2, InfiniteAdeleRing K)
local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "μD" => Measure.restrict (sourceKPAdelicTraceProduct K) (sourceKPAdelicFundamentalDomain K)
local notation "μY" => sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)
local notation "μA" => sourceKPArchHaar K hζ
local notation "μh" => sourceKPCuspProductHeightMeasure K
local notation "π" => sourceKPAutomorphicCompactMk K hζ
local notation "q" => sourceKPAutomorphicLevelMk K hζ
local notation "N" => sourceKPAdelicUpperLift K hζ
local notation "p" => sourceKPCuspArchRepresentativeCoordinates K hζ
local instance sourceResidualArchMeanAdelicMeasurable : MeasurableSpace 𝔸[K] := borel _
local instance sourceResidualArchMeanAdelicBorel : BorelSpace 𝔸[K] := ⟨rfl⟩
local instance sourceResidualArchMeanCircleMeasure : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

/-- The literal adelic trace orbit through an archimedean frame and a finite lift. -/
def sourceKPCompactTraceOrbit (W : Y → ℂ) (a : G) (qf : Gf) (z : 𝔸[K]) : ℂ :=
  W (π (q (N z * (a,qf))))

def sourceKPCompactTraceMean (W : Y → ℂ) (a : G) (qf : Gf) : ℂ :=
  ∫ z, sourceKPCompactTraceOrbit K hζ W a qf z ∂μD

variable (d : 𝓞 K) (hd : d ≠ 0)
local notation "E" => sourceKPCuspProductCoordinates K hζ d hd
local notation "e" => sourceKPCuspPrincipalTorusHomeomorph K d hd

local instance sourceResidualArchMeanPrincipalMeasurable :
    MeasurableSpace (SourceKPCuspPrincipalQuotient K d) := borel _
local instance sourceResidualArchMeanPrincipalBorel :
    BorelSpace (SourceKPCuspPrincipalQuotient K d) := ⟨rfl⟩

include hζ in
private theorem traceOrbit_translate_measurePreserving (u : 𝔸[K]) :
    MeasurePreserving (fun z : 𝔸[K] => e (QuotientAddGroup.mk (z+u)))
      μD (unitTorusHaar I) := by
  let Q := SourceKPCuspPrincipalQuotient K d
  have hq : MeasurePreserving (QuotientAddGroup.mk : 𝔸[K] → Q)
      μD (sourceKPCuspTraceHaar K d) := ⟨QuotientAddGroup.continuous_mk.measurable,rfl⟩
  have he := (sourceKPCuspPrincipalTorus_measurePreserving K d hζ hd).comp hq
  let t := e (QuotientAddGroup.mk u)
  have ht : MeasurePreserving (fun s : UnitAddTorus I => t+s)
      (unitTorusHaar I) (unitTorusHaar I) :=
    measurePreserving_pi _ _ fun i => measurePreserving_add_left AddCircle.haarAddCircle (t i)
  have h := ht.comp he
  have hfun : (fun s : UnitAddTorus I => t+s) ∘
      (e ∘ (QuotientAddGroup.mk : 𝔸[K] → Q)) =
      fun z : 𝔸[K] => e (QuotientAddGroup.mk (z+u)) := by
    funext z
    change e (QuotientAddGroup.mk u) + e (QuotientAddGroup.mk z) = _
    rw [QuotientAddGroup.mk_add,map_add,add_comm]
  rwa [hfun] at h

private theorem traceOrbit_eq_torus (W : Y → ℂ) (a : G) (qf : Gf)
    (hperiod : sourceKPCuspNativeFinitePeriod K hζ d qf)
    (x : I → ℝ) (y : V → ℝ) (hy : ∀ v, 0 < y v) (ha : p a = E (x,y))
    (z : 𝔸[K]) :
    sourceKPCompactTraceOrbit K hζ W a qf z =
      sourceKPCuspNativeTraceSlice K hζ d hd qf hperiod W y hy
        (e (QuotientAddGroup.mk (z+sourceKPCuspUnitCellAdelicPoint K d hd x))) := by
  let u := sourceKPCuspUnitCellAdelicPoint K d hd x
  let g := (N u).1 * sourceKPCuspHeightSection K hζ y hy
  have hu : N u * (sourceKPCuspHeightSection K hζ y hy,qf) = (g,qf) := by
    apply Prod.ext
    · rfl
    · change sourceKPFiniteAdeleUpperLift K hζ 0 * qf = qf
      rw [sourceKPFiniteAdeleUpperLift_zero, one_mul]
  have hg : p g = E (x,y) := sourceKPCuspArchRepresentativeCoordinates_native K hζ d hd x y hy
  rw [sourceKPCuspNativeTraceSlice_mk,sourceKPAdelicUpperLift_add,mul_assoc,hu]
  change W (π (q ((N z).1 * a,(N z).2 * qf))) =
    W (π (q ((N z).1 * g,(N z).2 * qf)))
  rw [← sourceKPCuspArchRepresentativeCoordinates_compact K hζ ((N z).2 * qf) ((N z).1*a),
    ← sourceKPCuspArchRepresentativeCoordinates_compact K hζ ((N z).2 * qf) ((N z).1*g),
    sourceKPCuspArchRepresentativeCoordinates_mul,sourceKPCuspArchRepresentativeCoordinates_mul,ha,hg]

private theorem nativeTraceSlice_measurable (W : Y → ℂ) (hW : Measurable W)
    (qf : Gf) (hperiod : sourceKPCuspNativeFinitePeriod K hζ d qf)
    (y : V → ℝ) (hy : ∀ v, 0 < y v) :
    Measurable (sourceKPCuspNativeTraceSlice K hζ d hd qf hperiod W y hy) := by
  let a := sourceKPCuspHeightSection K hζ y hy
  let g : SourceKPAdelicProjective K hζ := (a,qf)
  have hp := sourceKPCuspFinitePeriod_arch_change K hζ d qf hperiod a
  have hπ := (sourceKPAutomorphicCompactMk_isOpenQuotientMap K hζ).continuous.measurable
  have hc := (sourceKPCuspLevelCover_continuous K hζ d g hp hd).measurable
  exact hW.comp (hπ.comp (hc.comp (e).symm.continuous.measurable))

theorem sourceKPCompactTraceMean_eq_nativeCell (W : Y → ℂ) (hW : Measurable W)
    (a : G) (qf : Gf) (hperiod : sourceKPCuspNativeFinitePeriod K hζ d qf)
    (x : I → ℝ) (y : V → ℝ) (hy : ∀ v, 0 < y v) (ha : p a = E (x,y)) :
    sourceKPCompactTraceMean K hζ W a qf = sourceKPCuspNativeTraceCellCoeff K hζ d hd qf W 0 y := by
  let f := sourceKPCuspNativeTraceSlice K hζ d hd qf hperiod W y hy
  let u := sourceKPCuspUnitCellAdelicPoint K d hd x
  let A := fun z : 𝔸[K] => e (QuotientAddGroup.mk (z+u))
  have hmp := traceOrbit_translate_measurePreserving K hζ d hd u
  have hfm : StronglyMeasurable f := (nativeTraceSlice_measurable K hζ d hd W hW qf hperiod y hy).stronglyMeasurable
  have hi := integral_map_of_stronglyMeasurable (μ := μD) hmp.measurable hfm
  rw [hmp.map_eq] at hi
  calc
    _ = ∫ z, f (A z) ∂μD := integral_congr_ae
      (Filter.Eventually.of_forall (traceOrbit_eq_torus K hζ d hd W a qf hperiod x y hy ha))
    _ = ∫ t, f t ∂unitTorusHaar I := hi.symm
    _ = _ := sourceKPCuspNativeTraceSlice_zero_mode K hζ d hd qf hperiod W y hy

theorem sourceKPCuspArchCellHeight_quasiMeasurePreserving :
    Measure.QuasiMeasurePreserving (fun a : G => ((E).symm (p a)).2) μA μh := by
  obtain ⟨c,_hc,hm⟩ := sourceKPCuspProductCoordinates_map_productVolume K hζ d hd
  have hE : Measure.QuasiMeasurePreserving (E).symm (productVolume V)
      ((volume : Measure (I → ℝ)).prod μh) := by
    refine ⟨(E).symm.continuous.measurable,?_⟩
    rw [hm]
    exact Measure.smul_absolutelyContinuous
  exact
    Measure.quasiMeasurePreserving_snd.comp
      (hE.comp (sourceKPCuspArchRepresentativeCoordinates_measurePreserving K hζ).quasiMeasurePreserving)
/-- The height shape of a frame is independent of the principal period. -/
def sourceKPCuspRepresentativeHeight (a : G) : V → ℝ :=
  fun v => p a v 2

theorem sourceKPCuspRepresentativeHeight_eq (a : G) :
    ((E).symm (p a)).2 = sourceKPCuspRepresentativeHeight K hζ a := by
  funext v
  rw [sourceKPCuspRepresentativeHeight,← (E).apply_symm_apply (p a),
    sourceKPCuspProductCoordinates_height, (E).symm_apply_apply]

include hd in
/-- Haar-almost every archimedean frame has a trace-integrable orbit. -/
theorem sourceKPCompactTraceOrbit_integrable_ae
    (W : Y → ℂ) (hW : MemLp W 2 μY)
    (qf : Gf) (hperiod : sourceKPCuspNativeFinitePeriod K hζ d qf) :
    ∀ᵐ a ∂μA, Integrable (sourceKPCompactTraceOrbit K hζ W a qf) μD := by
  have hL : ∀ᵐ y ∂μh, ∀ hy : ∀ v, 0 < y v,
      MemLp (sourceKPCuspNativeTraceSlice K hζ d hd qf hperiod W y hy) 2
        (unitTorusHaar I) := by
    apply sourceKPCuspProductHeight_ae_of_compact K
    exact fun B hB hpos => sourceKPCuspNativeTraceSlice_memLp_ae K hζ d hd qf hperiod W hW B hB hpos
  have hheight := sourceKPCuspArchCellHeight_quasiMeasurePreserving K hζ d hd
  filter_upwards [hheight.ae hL, hheight.ae (sourceKPCuspProductHeight_ae_positive K)] with a ha hy
  let x := ((E).symm (p a)).1
  let y := ((E).symm (p a)).2
  have he : p a = E (x,y) := ((E).apply_symm_apply (p a)).symm
  let f := sourceKPCuspNativeTraceSlice K hζ d hd qf hperiod W y hy
  have hif : Integrable f (unitTorusHaar I) := (ha hy).integrable (by norm_num)
  have hmp := traceOrbit_translate_measurePreserving K hζ d hd (sourceKPCuspUnitCellAdelicPoint K d hd x)
  apply (hmp.integrable_comp_of_integrable hif).congr
  exact Filter.Eventually.of_forall fun z => (traceOrbit_eq_torus K hζ d hd W a qf hperiod x y hy he z).symm

end
end ArtinMatthews
