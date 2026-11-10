module

public import ArtinMatthews.StandardLocalFourier
public import ArtinMatthews.SourceLocalAdditiveModulus
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Mathlib.Topology.Algebra.IsOpenUnits
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The manuscript's actual finite multiplicative measure is the
pullback of the self-dual additive measure divided by the absolute value. -/

namespace ArtinMatthews.SourcePhysical

open NumberField IsDedekindDomain MeasureTheory Set Topology
open scoped NumberField ENNReal NNReal
noncomputable section
variable (K : Type) [Field K] [NumberField K]
variable (P : HeightOneSpectrum (𝓞 K))

local notation "k" => P.adicCompletion K

scoped instance sourceLocalCompletionUnitsBorelSpace : BorelSpace kˣ := by
  constructor
  change (borel k).comap (Units.val : kˣ → k) = borel kˣ
  rw [← borel_comap]
  congr 1
  exact Units.isEmbedding_val₀.isInducing.eq_induced.symm

theorem sourceLocalUnits_measurableEmbedding : MeasurableEmbedding (Units.val : kˣ → k) :=
  (IsOpenUnits.isOpenEmbedding_unitsVal (M := k)).measurableEmbedding

theorem sourceLocalUnits_range : range (Units.val : kˣ → k) = ({0} : Set k)ᶜ := by
  ext x
  change IsUnit x ↔ x ≠ 0
  exact isUnit_iff_ne_zero

def sourceLocalMulDensity (x : k) : ℝ≥0∞ := (‖x‖₊⁻¹ : ℝ≥0)

theorem sourceLocalMulDensity_eq (x : k) :
    sourceLocalMulDensity K P x = ENNReal.ofReal ‖x‖⁻¹ := by
  rw [sourceLocalMulDensity, ← ENNReal.ofReal_coe_nnreal, NNReal.coe_inv]
  rfl

theorem sourceLocalMulDensity_measurable : Measurable (sourceLocalMulDensity K P) := by
  rw [show sourceLocalMulDensity K P = fun x : k => ENNReal.ofReal ‖x‖⁻¹ from
    funext (sourceLocalMulDensity_eq K P)]
  exact continuous_norm.measurable.inv.ennreal_ofReal

def sourceLocalMulMeasure : Measure kˣ :=
  ((sourceLocalSelfDual K P).withDensity (sourceLocalMulDensity K P)).comap Units.val

theorem sourceLocalMulMeasure_apply (s : Set kˣ) (hs : MeasurableSet s) :
    sourceLocalMulMeasure K P s =
      ∫⁻ x in Units.val '' s, sourceLocalMulDensity K P x ∂sourceLocalSelfDual K P := by
  rw [sourceLocalMulMeasure, (sourceLocalUnits_measurableEmbedding K P).comap_apply,
    withDensity_apply _ ((sourceLocalUnits_measurableEmbedding K P).measurableSet_image.mpr hs)]

theorem sourceLocalMulMeasure_map_val :
    (sourceLocalMulMeasure K P).map (Units.val : kˣ → k) =
      (sourceLocalSelfDual K P).withDensity (sourceLocalMulDensity K P) := by
  rw [sourceLocalMulMeasure, (sourceLocalUnits_measurableEmbedding K P).map_comap,
    sourceLocalUnits_range]
  apply Measure.restrict_eq_self_of_ae_mem
  rw [ae_iff]
  have h0 : ({x : k | ¬ x ∈ ({0} : Set k)ᶜ}) = ({0} : Set k) := by simp
  rw [h0, withDensity_apply _ (measurableSet_singleton (0 : k))]
  calc
    _ = ∫⁻ _ in ({0} : Set k), (0 : ℝ≥0∞) ∂sourceLocalSelfDual K P := by
      apply setLIntegral_congr_fun (measurableSet_singleton _)
      intro x hx
      simp [mem_singleton_iff.mp hx, sourceLocalMulDensity]
    _ = 0 := lintegral_zero

theorem sourceLocalMulDensity_measure_map_mul (t : kˣ) :
    ((sourceLocalSelfDual K P).withDensity (sourceLocalMulDensity K P)).map
        (fun x => (t : k) * x) =
      (sourceLocalSelfDual K P).withDensity (sourceLocalMulDensity K P) := by
  let w := sourceLocalMulDensity K P
  let μ := sourceLocalSelfDual K P
  let g : k → k := fun x => (t : k) * x
  have hg : Measurable g := (continuous_const.mul continuous_id).measurable
  have hw : Measurable w := sourceLocalMulDensity_measurable K P
  have hwg (x : k) : (‖(t : k)‖₊ : ℝ≥0∞) * w (g x) = w x := by
    have hinv (a b : ℝ≥0) : (a * b)⁻¹ = a⁻¹ * b⁻¹ := smul_inv₀ a b
    have hn : ‖(t : k)‖₊ ≠ 0 := nnnorm_ne_zero_iff.mpr t.ne_zero
    simp only [w, g, sourceLocalMulDensity, ← ENNReal.coe_mul]
    rw [nnnorm_mul, hinv, mul_inv_cancel_left₀ hn]
  have ht : ‖(t : k)‖₊ * ‖((t⁻¹ : kˣ) : k)‖₊ = 1 := by
    rw [← nnnorm_mul, t.mul_inv, nnnorm_one]
  change (μ.withDensity w).map g = μ.withDensity w
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf hg]
  change (∫⁻ x, (f ∘ g) x ∂μ.withDensity w) = _
  rw [lintegral_withDensity_eq_lintegral_mul μ hw (hf.comp hg),
    lintegral_withDensity_eq_lintegral_mul μ hw hf]
  change (∫⁻ x, w x * f (g x) ∂μ) = ∫⁻ x, w x * f x ∂μ
  calc
    _ = ∫⁻ x, (‖(t : k)‖₊ : ℝ≥0∞) * (w (g x) * f (g x)) ∂μ := by
      apply lintegral_congr
      intro x
      rw [← mul_assoc, hwg]
    _ = (‖(t : k)‖₊ : ℝ≥0∞) * ∫⁻ y, w y * f y ∂μ.map g := by
      let F : k → ℝ≥0∞ := fun y => w y * f y
      have hF : Measurable F := hw.mul hf
      calc
        _ = (‖(t : k)‖₊ : ℝ≥0∞) * ∫⁻ x, F (g x) ∂μ :=
          lintegral_const_mul _ (hF.comp hg)
        _ = _ := congrArg (fun a : ℝ≥0∞ => (‖(t : k)‖₊ : ℝ≥0∞) * a)
          (lintegral_map hF hg).symm
    _ = _ := by
      rw [show μ.map g = _ from sourceLocalSelfDual_map_mul K P t,
        lintegral_smul_measure, smul_eq_mul, ← mul_assoc, ← ENNReal.coe_mul,
        ht, ENNReal.coe_one, one_mul]

theorem sourceLocalMulMeasure_isMulLeftInvariant :
    (sourceLocalMulMeasure K P).IsMulLeftInvariant := by
  constructor
  intro t
  let μ := sourceLocalMulMeasure K P
  let v : kˣ → k := Units.val
  let g : k → k := fun x => (t : k) * x
  let h : kˣ → kˣ := fun u => t * u
  have hv : MeasurableEmbedding v := sourceLocalUnits_measurableEmbedding K P
  have hg : Measurable g := (continuous_const.mul continuous_id).measurable
  have hh : Measurable h := (continuous_const.mul continuous_id).measurable
  change μ.map h = μ
  apply hv.map_injective
  calc
    (μ.map h).map v = (μ.map v).map g := by
      rw [Measure.map_map hv.measurable hh, Measure.map_map hg hv.measurable]
      rfl
    _ = μ.map v := by
      change ((sourceLocalMulMeasure K P).map (Units.val : kˣ → k)).map g =
        (sourceLocalMulMeasure K P).map (Units.val : kˣ → k)
      rw [sourceLocalMulMeasure_map_val]
      exact sourceLocalMulDensity_measure_map_mul K P t

end
end ArtinMatthews.SourcePhysical
