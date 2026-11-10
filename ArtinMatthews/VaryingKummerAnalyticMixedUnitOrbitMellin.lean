module

public import ArtinMatthews.VaryingKummerAnalyticMixedPartialDedekind
public import ArtinMatthews.VaryingKummerAnalyticUnitUnfoldingComplex
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

/-! Complex Mellin integration of the actual full unit orbit in arbitrary
signature, retaining the genuine roots-of-unity multiplicity. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField MeasureTheory Set Filter
open NumberField.Units NumberField.Units.dirichletUnitTheorem
open scoped NumberField nonZeroDivisors Classical BigOperators ENNReal
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem mixedRadialKernel_unit_translate (a : K) (z : (𝓞 K)ˣ)
    (s : ℂ) (t : ℝ) (u : logSpace K) :
    mixedRadialKernel K ((z : K)*a) s t u =
      mixedRadialKernel K a s t (logEmbedding K (Additive.ofMul z)+u) := by
  unfold mixedRadialKernel mixedArchEnergy
  simp only [map_mul, mixedPlaceWeight_add, mixedPlaceWeight_unit]
  congr 5
  apply Finset.sum_congr rfl
  intro w _
  ring

def mixedUnitOrbitMellinKernel (a : K) (s : ℂ) (p : ℝ × logSpace K) : ℂ :=
  ∑' z : (𝓞 K)ˣ, mixedRadialKernel K ((z : K)*a) s p.1 p.2

theorem mixedUnitOrbitMellinKernel_measurable (a : K) (s : ℂ) :
    Measurable (mixedUnitOrbitMellinKernel K a s) := by
  let : Countable K := Finsupp.Countable.of_moduleFinite (R := ℚ)
  let : Countable (𝓞 K) := NumberField.RingOfIntegers.coe_injective.countable
  let : Countable (𝓞 K)ˣ := Units.val_injective.countable
  exact Measurable.tsum (fun z => mixedRadialKernel_measurable K ((z : K)*a) s)

theorem mixedUnitOrbitMellinKernel_enorm_le (a : K) (s : ℂ)
    {t : ℝ} (ht : 0 < t) (u : logSpace K) :
    ‖mixedUnitOrbitMellinKernel K a s (t,u)‖ₑ ≤
      ENNReal.ofReal (t^((Module.finrank ℚ K : ℝ)*s.re/2-1)) *
        ∑' z : (𝓞 K)ˣ, mixedArchGaussian K ((z : K)*a) t u := by
  unfold mixedUnitOrbitMellinKernel
  calc
    _ ≤ ∑' z : (𝓞 K)ˣ, ‖mixedRadialKernel K ((z : K)*a) s t u‖ₑ :=
      enorm_tsum_le_tsum_enorm
    _ = _ := by
      simp_rw [← ofReal_norm, mixedRadialKernel_norm K _ s ht,
        mixedRealRadialKernel, ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _)]
      exact ENNReal.tsum_mul_left

theorem mixedUnitOrbitMellinKernel_enorm_integral_le {a : K} (ha : a ≠ 0)
    {s : ℂ} (hs : 0 < s.re) :
    (∫⁻ p, ‖mixedUnitOrbitMellinKernel K a s p‖ₑ
      ∂(volume.restrict (Ioi 0)).prod (volume.restrict (mixedUnitLogDomain K))) ≤
      (torsionOrder K : ℝ≥0∞) *
        ENNReal.ofReal (mixedRealHeckeFactor K s.re * |(Algebra.norm ℚ a : ℝ)|^(-s.re)) := by
  rw [lintegral_prod _ (mixedUnitOrbitMellinKernel_measurable K a s).enorm.aemeasurable]
  calc
    _ ≤ ∫⁻ t in Ioi 0, ∫⁻ u in mixedUnitLogDomain K,
        ENNReal.ofReal (t^((Module.finrank ℚ K : ℝ)*s.re/2-1)) *
          ∑' z : (𝓞 K)ˣ, mixedArchGaussian K ((z : K)*a) t u := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact lintegral_mono (fun u => mixedUnitOrbitMellinKernel_enorm_le K a s ht u)
    _ = _ := by
      simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        mixedArchGaussian_units_unfold K a]
      simp_rw [mul_left_comm _ (torsionOrder K : ℝ≥0∞)]
      rw [lintegral_const_mul' _ _ (ENNReal.natCast_ne_top _),
        mixedArchGaussian_mellin_lintegral K ha hs]
      rfl

theorem mixedUnitOrbitMellinKernel_integrable {a : K} (ha : a ≠ 0)
    {s : ℂ} (hs : 0 < s.re) :
    Integrable (mixedUnitOrbitMellinKernel K a s)
      ((volume.restrict (Ioi 0)).prod (volume.restrict (mixedUnitLogDomain K))) := by
  refine ⟨(mixedUnitOrbitMellinKernel_measurable K a s).aestronglyMeasurable, ?_⟩
  exact lt_of_le_of_lt (mixedUnitOrbitMellinKernel_enorm_integral_le K ha hs)
    (ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) ENNReal.ofReal_lt_top)

theorem mixedUnitOrbitMellinKernel_integral {a : K} (ha : a ≠ 0)
    {s : ℂ} (hs : 0 < s.re) :
    (∫ p, mixedUnitOrbitMellinKernel K a s p
      ∂(volume.restrict (Ioi 0)).prod (volume.restrict (mixedUnitLogDomain K))) =
      (torsionOrder K : ℂ) * (mixedRadialJacobian K : ℂ) * mixedGammaFactor K s *
        ((|(Algebra.norm ℚ a : ℝ)| : ℝ) : ℂ)^(-s) := by
  rw [integral_prod _ (mixedUnitOrbitMellinKernel_integrable K ha hs)]
  have hi := (mixedRadialKernel_product_integrable K ha hs).prod_right_ae
  calc
    _ = ∫ t in Ioi 0, (torsionOrder K : ℂ) * ∫ u, mixedRadialKernel K a s t u := by
      apply integral_congr_ae
      filter_upwards [hi] with t ht
      simp only [mixedUnitOrbitMellinKernel, mixedRadialKernel_unit_translate]
      apply mixedUnitLog_unfold_complex K _ _ ht
      exact (mixedRadialKernel_measurable K a s).comp (measurable_const.prodMk measurable_id)
    _ = _ := by
      rw [integral_const_mul, mixedRadialKernel_mellin K ha hs]
      ring

end
end ArtinMatthews.VaryingKummerAnalytic
