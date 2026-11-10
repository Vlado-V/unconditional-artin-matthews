module

public import ArtinMatthews.SourceAdelicFundamentalDomain
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
public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Exact rational periodization for an explicit additive Haar measure.
The same measure occurs on the fundamental domain and the full adele ring. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory
open OAI.RepresentationTheory.Weil.AdelicSplitting
open scoped NumberField AdeleRing Topology ENNReal
noncomputable section
variable (K : Type) [Field K] [NumberField K]

local instance : MeasurableSpace 𝔸[K] := borel 𝔸[K]
local instance : BorelSpace 𝔸[K] := ⟨rfl⟩

variable (μ : Measure 𝔸[K]) [μ.IsAddHaarMeasure]

def sourceKPAdelicPeriodization (f : 𝔸[K] → ℂ) (a : 𝔸[K]) : ℂ :=
  ∑' q : K, f (a + algebraMap K 𝔸[K] q)

theorem sourceKPAdelicPeriodization_eq_subgroup (f : 𝔸[K] → ℂ) (a : 𝔸[K]) :
    sourceKPAdelicPeriodization K f a =
      ∑' q : sourceKPAdelicRationals K, f ((q : 𝔸[K]) + a) := by
  unfold sourceKPAdelicPeriodization
  rw [← (sourceKPRationalAdeleEquiv K).toEquiv.tsum_eq (fun q => f ((q : 𝔸[K]) + a))]
  apply tsum_congr
  intro q
  change f (a + algebraMap K 𝔸[K] q) = f (algebraMap K 𝔸[K] q + a)
  rw [add_comm]

theorem sourceKPAdelicPeriodization_norm_lintegral (f : 𝔸[K] → ℂ) :
    (∑' q : sourceKPAdelicRationals K,
      ∫⁻ a in sourceKPAdelicFundamentalDomain K, ‖f ((q : 𝔸[K]) + a)‖ₑ ∂μ) =
        ∫⁻ a, ‖f a‖ₑ ∂μ :=
  ((sourceKPAdelicFundamentalDomain_isFundamental K μ).lintegral_eq_tsum'' (fun a => ‖f a‖ₑ)).symm

theorem sourceKPAdelicPeriodization_integrable (f : 𝔸[K] → ℂ) (hf : Integrable f μ) :
    IntegrableOn (sourceKPAdelicPeriodization K f) (sourceKPAdelicFundamentalDomain K) μ := by
  let D := sourceKPAdelicFundamentalDomain K
  have hi (q : sourceKPAdelicRationals K) : Integrable (fun a : 𝔸[K] => f ((q : 𝔸[K]) + a)) μ :=
    hf.comp_add_left _
  have hm (q : sourceKPAdelicRationals K) :
      AEStronglyMeasurable (fun a : 𝔸[K] => f ((q : 𝔸[K]) + a)) (μ.restrict D) :=
    (hi q).restrict.aestronglyMeasurable
  have hn : (∑' q : sourceKPAdelicRationals K,
      ∫⁻ a in D, ‖f ((q : 𝔸[K]) + a)‖ₑ ∂μ) ≠ ∞ := by
    rw [sourceKPAdelicPeriodization_norm_lintegral K μ]
    exact hf.2.ne
  have ht : (∫⁻ a, ∑' q : sourceKPAdelicRationals K, ‖f ((q : 𝔸[K]) + a)‖ₑ ∂μ.restrict D) < ∞ := by
    rw [lintegral_tsum (fun q => (hm q).enorm)]
    exact lt_top_iff_ne_top.mpr hn
  have hs : Integrable (fun a : 𝔸[K] => ∑' q : sourceKPAdelicRationals K, f ((q : 𝔸[K]) + a)) (μ.restrict D) :=
    ⟨AEStronglyMeasurable.tsum hm,
      lt_of_le_of_lt (lintegral_mono (fun _ => enorm_tsum_le_tsum_enorm)) ht⟩
  apply hs.congr
  exact Filter.Eventually.of_forall (fun a => (sourceKPAdelicPeriodization_eq_subgroup K f a).symm)

theorem sourceKPAdelicHaarUnfolding (f : 𝔸[K] → ℂ) (hf : Integrable f μ) :
    (∫ a in sourceKPAdelicFundamentalDomain K, sourceKPAdelicPeriodization K f a ∂μ) =
      ∫ a, f a ∂μ := by
  have hm (q : sourceKPAdelicRationals K) :
      AEStronglyMeasurable (fun a : 𝔸[K] => f ((q : 𝔸[K]) + a))
        (μ.restrict (sourceKPAdelicFundamentalDomain K)) :=
    (hf.comp_add_left (q : 𝔸[K])).restrict.aestronglyMeasurable
  have hn : (∑' q : sourceKPAdelicRationals K,
      ∫⁻ a in sourceKPAdelicFundamentalDomain K, ‖f ((q : 𝔸[K]) + a)‖ₑ ∂μ) ≠ ∞ := by
    rw [sourceKPAdelicPeriodization_norm_lintegral K μ]
    exact hf.2.ne
  calc
    _ = ∫ a in sourceKPAdelicFundamentalDomain K,
        ∑' q : sourceKPAdelicRationals K, f ((q : 𝔸[K]) + a) ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (sourceKPAdelicPeriodization_eq_subgroup K f)
    _ = ∑' q : sourceKPAdelicRationals K,
        ∫ a in sourceKPAdelicFundamentalDomain K, f ((q : 𝔸[K]) + a) ∂μ := integral_tsum hm hn
    _ = _ := ((sourceKPAdelicFundamentalDomain_isFundamental K μ).integral_eq_tsum'' f hf).symm

theorem sourceKPAdelicLIntegralUnfolding (f : 𝔸[K] → ℝ≥0∞) (hf : AEMeasurable f μ) :
    (∫⁻ a in sourceKPAdelicFundamentalDomain K,
      ∑' q : K, f (a + algebraMap K 𝔸[K] q) ∂μ) = ∫⁻ a, f a ∂μ := by
  have hm (q : sourceKPAdelicRationals K) :
      AEMeasurable (fun a : 𝔸[K] => f ((q : 𝔸[K]) + a))
        (μ.restrict (sourceKPAdelicFundamentalDomain K)) :=
    (hf.comp_quasiMeasurePreserving (measurePreserving_add_left μ (q : 𝔸[K])).quasiMeasurePreserving).mono_measure
      Measure.restrict_le_self
  have he (a : 𝔸[K]) : (∑' q : K, f (a + algebraMap K 𝔸[K] q)) =
      ∑' q : sourceKPAdelicRationals K, f ((q : 𝔸[K]) + a) := by
    rw [← (sourceKPRationalAdeleEquiv K).toEquiv.tsum_eq (fun q => f ((q : 𝔸[K]) + a))]
    apply tsum_congr
    intro q
    change f (a + algebraMap K 𝔸[K] q) = f (algebraMap K 𝔸[K] q + a)
    rw [add_comm]
  calc
    _ = ∫⁻ a in sourceKPAdelicFundamentalDomain K,
        ∑' q : sourceKPAdelicRationals K, f ((q : 𝔸[K]) + a) ∂μ := lintegral_congr he
    _ = ∑' q : sourceKPAdelicRationals K,
        ∫⁻ a in sourceKPAdelicFundamentalDomain K, f ((q : 𝔸[K]) + a) ∂μ := lintegral_tsum hm
    _ = _ := ((sourceKPAdelicFundamentalDomain_isFundamental K μ).lintegral_eq_tsum'' f).symm

theorem sourceKPAdelicIntegrable_of_periodization (f : 𝔸[K] → ℂ)
    (hf : AEStronglyMeasurable f μ)
    (hperiod : (∫⁻ a in sourceKPAdelicFundamentalDomain K,
      ∑' q : K, ENNReal.ofReal ‖f (a + algebraMap K 𝔸[K] q)‖ ∂μ) < ∞) :
    Integrable f μ := by
  refine ⟨hf, ?_⟩
  have h := sourceKPAdelicLIntegralUnfolding K μ (fun a => ‖f a‖ₑ) hf.enorm
  have hp : (∫⁻ a in sourceKPAdelicFundamentalDomain K,
      ∑' q : K, ‖f (a + algebraMap K 𝔸[K] q)‖ₑ ∂μ) < ∞ := by
    simpa only [ofReal_norm] using hperiod
  rw [h] at hp
  exact hp

theorem sourceKPAdelicFundamentalDomain_measure_pos :
    0 < μ (sourceKPAdelicFundamentalDomain K) := by
  exact pos_iff_ne_zero.mpr (IsAddFundamentalDomain.measure_ne_zero (NeZero.ne μ)
    (sourceKPAdelicFundamentalDomain_isFundamental K μ))

theorem sourceKPAdelicFundamentalDomain_measure_lt_top :
    μ (sourceKPAdelicFundamentalDomain K) < ∞ :=
  lt_of_le_of_lt (measure_mono (sourceKPAdelicFundamentalDomain_subset_compact K))
    (CompactQuotient.Construction.isCompact_adelicCompactRepresentatives K).measure_lt_top

end
end ArtinMatthews
