module

public import ArtinMatthews.SourceSLocalOtherTensor
public import ArtinMatthews.SourceSLocalWholeSplitMeasure
public import Mathlib.Analysis.CStarAlgebra.Classes
public import ArtinMatthews.SourceSLocalSheetBorel
public import ArtinMatthews.SourceSLocalSheetTopology
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


set_option backward.privateInPublic true
@[expose] public section

/-! Weighted L1 and the exact Mellin product on the original retained
product measure, given the one-place input estimates. -/

namespace ArtinMatthews.SourcePhysical
open NumberField NumberField.InfinitePlace IsDedekindDomain MeasureTheory
open scoped NumberField BigOperators Classical
noncomputable section

variable {K : Type} [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K))) (v : InfinitePlace K)
variable [∀ w : InfinitePlace K, MeasurableSpace w.Completionˣ]
variable [∀ p : S, MeasurableSpace (p.val.adicCompletion K)ˣ]
variable (μarch : ∀ w : InfinitePlace K, Measure w.Completionˣ)
variable (μf : ∀ p : S, Measure (p.val.adicCompletion K)ˣ)
variable (garch : ∀ w : InfinitePlace K, w.Completionˣ → ℂ)
variable (gf : ∀ p : S, (p.val.adicCompletion K)ˣ → ℂ)

theorem measurable_sourceSheetOtherTensor
    (harch : ∀ w : {w : InfinitePlace K // w ≠ v}, Measurable (garch w.val))
    (hf : ∀ p : S, Measurable (gf p)) :
    Measurable (sourceSheetOtherTensor S v garch gf) := by
  unfold sourceSheetOtherTensor
  exact (Finset.measurable_prod _ fun w _ =>
    (harch w).comp ((measurable_pi_apply w).comp measurable_fst)).mul
      (Finset.measurable_prod _ fun p _ => (hf p).comp ((measurable_pi_apply p).comp measurable_snd))

theorem measurable_sourceSheetOtherMellinIntegrand
    [∀ w : InfinitePlace K, BorelSpace w.Completionˣ]
    [∀ p : S, BorelSpace (p.val.adicCompletion K)ˣ]
    (harch : ∀ w : {w : InfinitePlace K // w ≠ v}, Measurable (garch w.val))
    (hf : ∀ p : S, Measurable (gf p)) (s : ℂ) :
    Measurable (sourceSheetOtherMellinIntegrand S v garch gf s) := by
  let : BorelSpace (SNormOneOtherUnits S v) := sourceSheetOtherUnits_product_borel S v
  let N := sourceSheetOtherNorm S v
  have hp (y : SNormOneOtherUnits S v) : 0 < N y := sourceSheetOtherNorm_pos S v y
  have hlog : Continuous (fun y => Real.log (N y)) :=
    (continuous_sourceSheetOtherNorm S v).log (fun y => (hp y).ne')
  have he : Continuous (fun y => Complex.exp ((Real.log (N y) : ℂ) * s)) :=
    Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp hlog).mul continuous_const)
  have hpow : (fun y => (N y : ℂ) ^ s) = fun y => Complex.exp ((Real.log (N y) : ℂ) * s) := by
    funext y
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (hp y).ne'),
      ← Complex.ofReal_log (hp y).le]
  unfold sourceSheetOtherMellinIntegrand
  apply (measurable_sourceSheetOtherTensor S v garch gf harch hf).mul
  change Measurable (fun y => (N y : ℂ) ^ s)
  rw [hpow]
  exact he.measurable

/-- The Mellin integral of the retained tensor with the actual local product measure. -/
def sourceSheetOtherMellin (s : ℂ) : ℂ :=
  ∫ y, sourceSheetOtherMellinIntegrand S v garch gf s y ∂sourceSheetOtherMeasure S v μarch μf

variable [IsTotallyComplex K]
variable [∀ w, SigmaFinite (μarch w)] [∀ p, SigmaFinite (μf p)]

theorem sourceSheetOtherTensor_weighted_norm_integrable (σ : ℝ)
    (harch : ∀ w : {w : InfinitePlace K // w ≠ v},
      Integrable (fun z => ‖garch w.val z‖ * sourceSheetArchNorm w.val z ^ σ) (μarch w.val))
    (hf : ∀ p : S, Integrable (fun z => ‖gf p z‖ * sourceSheetFiniteNorm S p z ^ σ) (μf p)) :
    Integrable (fun y => ‖sourceSheetOtherTensor S v garch gf y‖ * sourceSheetOtherNorm S v y ^ σ)
      (sourceSheetOtherMeasure S v μarch μf) := by
  have ha : Integrable
      (fun x : ∀ w : {w : InfinitePlace K // w ≠ v}, w.val.Completionˣ =>
        ∏ w, ‖garch w.val (x w)‖ * sourceSheetArchNorm w.val (x w) ^ σ)
      (Measure.pi (fun w : {w : InfinitePlace K // w ≠ v} => μarch w.val)) :=
    Integrable.fintype_prod_dep
      (μ := fun w : {w : InfinitePlace K // w ≠ v} => μarch w.val)
      (f := fun (w : {w : InfinitePlace K // w ≠ v}) (z : w.val.Completionˣ) =>
        ‖garch w.val z‖ * sourceSheetArchNorm w.val z ^ σ) harch
  have hb : Integrable (fun x : ∀ p : S, (p.val.adicCompletion K)ˣ =>
      ∏ p, ‖gf p (x p)‖ * sourceSheetFiniteNorm S p (x p) ^ σ) (Measure.pi μf) :=
    Integrable.fintype_prod_dep (μ := μf)
      (f := fun (p : S) (z : (p.val.adicCompletion K)ˣ) =>
        ‖gf p z‖ * sourceSheetFiniteNorm S p z ^ σ) hf
  exact (ha.mul_prod hb).congr (Filter.Eventually.of_forall fun y =>
    (sourceSheetOtherTensor_weighted_norm_eq_prod S v garch gf σ y).symm)

theorem sourceSheetOtherMellinIntegrand_integrable
    [∀ w : InfinitePlace K, BorelSpace w.Completionˣ]
    [∀ p : S, BorelSpace (p.val.adicCompletion K)ˣ]
    (s : ℂ)
    (harch_meas : ∀ w : {w : InfinitePlace K // w ≠ v}, Measurable (garch w.val))
    (hf_meas : ∀ p : S, Measurable (gf p))
    (harch : ∀ w : {w : InfinitePlace K // w ≠ v},
      Integrable (fun z => ‖garch w.val z‖ * sourceSheetArchNorm w.val z ^ s.re) (μarch w.val))
    (hf : ∀ p : S, Integrable (fun z => ‖gf p z‖ * sourceSheetFiniteNorm S p z ^ s.re) (μf p)) :
    Integrable (sourceSheetOtherMellinIntegrand S v garch gf s) (sourceSheetOtherMeasure S v μarch μf) := by
  have hm := measurable_sourceSheetOtherMellinIntegrand S v garch gf harch_meas hf_meas s
  apply (integrable_norm_iff hm.aestronglyMeasurable).mp
  exact (sourceSheetOtherTensor_weighted_norm_integrable S v μarch μf garch gf s.re harch hf).congr
    (Filter.Eventually.of_forall fun y => (sourceSheetOtherMellinIntegrand_norm S v garch gf s y).symm)

theorem sourceSheetOtherMellin_eq_prod (s : ℂ) :
    sourceSheetOtherMellin S v μarch μf garch gf s =
      (∏ w : {w : InfinitePlace K // w ≠ v},
        ∫ z, garch w.val z * (sourceSheetArchNorm w.val z : ℂ) ^ s ∂μarch w.val) *
      ∏ p : S, ∫ z, gf p z * (sourceSheetFiniteNorm S p z : ℂ) ^ s ∂μf p := by
  let A (x : ∀ w : {w : InfinitePlace K // w ≠ v}, w.val.Completionˣ) :=
    ∏ w, garch w.val (x w) * (sourceSheetArchNorm w.val (x w) : ℂ) ^ s
  let B (x : ∀ p : S, (p.val.adicCompletion K)ˣ) :=
    ∏ p, gf p (x p) * (sourceSheetFiniteNorm S p (x p) : ℂ) ^ s
  have hfun : sourceSheetOtherMellinIntegrand S v garch gf s =
      fun y : SNormOneOtherUnits S v => A y.1 * B y.2 :=
    funext (sourceSheetOtherMellinIntegrand_eq_prod S v garch gf s)
  rw [sourceSheetOtherMellin, hfun, sourceSheetOtherMeasure, integral_prod_mul A B]
  congr 1
  · exact integral_fintype_prod_eq_prod
      (μ := fun w : {w : InfinitePlace K // w ≠ v} => μarch w.val)
      (fun (w : {w : InfinitePlace K // w ≠ v}) (z : w.val.Completionˣ) =>
        garch w.val z * (sourceSheetArchNorm w.val z : ℂ) ^ s)
  · exact integral_fintype_prod_eq_prod (μ := μf)
      (fun (p : S) (z : (p.val.adicCompletion K)ˣ) => gf p z * (sourceSheetFiniteNorm S p z : ℂ) ^ s)

end
end ArtinMatthews.SourcePhysical
