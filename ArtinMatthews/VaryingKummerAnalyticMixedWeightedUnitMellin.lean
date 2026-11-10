module

public import ArtinMatthews.VaryingKummerAnalyticMixedUnitOrbitMellin
public import ArtinMatthews.VaryingKummerAnalyticDedekindSeriesPartial
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
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Basify
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
public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Absolute convergence and genuine weighted ideal-class Mellin unfolding.
The finite-series argument adapts OpenAI PrimePackets/UnitOrbitIntegrals to
our checked mixed-signature radial integral and full unit group. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField MeasureTheory Set Filter
open NumberField.Units NumberField.Units.dirichletUnitTheorem
open scoped NumberField nonZeroDivisors Classical BigOperators ENNReal
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
lemma tsum_lintegral_mixedUnitOrbitMellinKernel_ne_top
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {s : ℂ} (hs : 1 < s.re) :
    (∑' J : integralIdealClassFiber I, ∫⁻ p,
      ‖mixedUnitOrbitMellinKernel K (idealElementRepresentative I J).1.1 s p‖ₑ
        ∂(volume.restrict (Ioi 0)).prod (volume.restrict (mixedUnitLogDomain K))) ≠ ⊤ := by
  let C : ℝ≥0∞ := (torsionOrder K : ℝ≥0∞) *
    ENNReal.ofReal (mixedRealHeckeFactor K s.re * (FractionalIdeal.absNorm I.val:ℝ)^(-s.re))
  have HJ (J : integralIdealClassFiber I) :
      (∫⁻ p, ‖mixedUnitOrbitMellinKernel K (idealElementRepresentative I J).1.1 s p‖ₑ
        ∂(volume.restrict (Ioi 0)).prod (volume.restrict (mixedUnitLogDomain K))) ≤
      C * ENNReal.ofReal ((FractionalIdeal.absNorm J.1.val:ℝ)^(-s.re)) := by
    have H := mixedUnitOrbitMellinKernel_enorm_integral_le K
      (idealElementRepresentative I J).1.ne_zero (lt_trans zero_lt_one hs)
    rw [idealElementRepresentative_absNorm,
      Real.mul_rpow (fractionalIdeal_absNorm_pos I).le (fractionalIdeal_absNorm_pos J.1).le,
      ← mul_assoc,ENNReal.ofReal_mul (mul_nonneg
        ((mixedRealHeckeFactor_pos K (lt_trans zero_lt_one hs)).le)
        (Real.rpow_nonneg (fractionalIdeal_absNorm_pos I).le _)),← mul_assoc] at H
    exact H
  apply ne_top_of_le_ne_top _ (ENNReal.tsum_le_tsum HJ)
  rw [ENNReal.tsum_mul_left]
  apply ENNReal.mul_ne_top _ (mixedPartialDedekindPositive_ne_top K I hs)
  exact ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top

lemma tsum_lintegral_weightedMixedUnitOrbitMellinKernel_ne_top
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (w : integralIdealClassFiber I → ℂ) (hw : ∀ J, ‖w J‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    (∑' J : integralIdealClassFiber I, ∫⁻ p,
      ‖w J * mixedUnitOrbitMellinKernel K (idealElementRepresentative I J).1.1 s p‖ₑ
        ∂(volume.restrict (Ioi 0)).prod (volume.restrict (mixedUnitLogDomain K))) ≠ ⊤ := by
  apply ne_top_of_le_ne_top (tsum_lintegral_mixedUnitOrbitMellinKernel_ne_top K I hs)
  apply ENNReal.tsum_le_tsum
  intro J
  apply lintegral_mono
  intro p
  dsimp only
  rw [enorm_mul]
  apply mul_le_of_le_one_left (by positivity)
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_one.mpr (hw J)

 

theorem integral_weightedMixedIdealUnitOrbits
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (w : integralIdealClassFiber I → ℂ) (hw : ∀ J, ‖w J‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    (∫ p, ∑' J : integralIdealClassFiber I,
      w J * mixedUnitOrbitMellinKernel K (idealElementRepresentative I J).1.1 s p
        ∂(volume.restrict (Ioi 0)).prod (volume.restrict (mixedUnitLogDomain K))) =
      (torsionOrder K : ℂ) *
        ((mixedRadialJacobian K : ℂ) * mixedGammaFactor K s) *
        ((FractionalIdeal.absNorm I.val:ℝ):ℂ)^(-s) *
          ∑' J : integralIdealClassFiber I,
            w J * ((FractionalIdeal.absNorm J.1.val:ℝ):ℂ)^(-s) := by
  let : Countable K := Finsupp.Countable.of_moduleFinite (R := ℚ)
  let : Countable Kˣ := Units.val_injective.countable
  let : Countable (nonzeroIdealElements I) := by
    change Countable {a : Kˣ // (a : K) ∈ (I : FractionalIdeal (𝓞 K)⁰ K)}
    infer_instance
  let : Countable (integralIdealClassFiber I) := (relativeElementClassMap_surjective I).countable
  rw [integral_tsum (fun J =>
    ((mixedUnitOrbitMellinKernel_measurable K _ s).const_mul (w J)).aestronglyMeasurable)
    (tsum_lintegral_weightedMixedUnitOrbitMellinKernel_ne_top K I w hw hs)]
  simp_rw [integral_const_mul,
    mixedUnitOrbitMellinKernel_integral K (idealElementRepresentative I _).1.ne_zero
      (lt_trans zero_lt_one hs),idealElementRepresentative_absNorm,
    Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (fractionalIdeal_absNorm_pos I).le
      (fractionalIdeal_absNorm_pos _).le]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro J
  ring


theorem integrable_weightedMixedIdealUnitOrbits
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (w : integralIdealClassFiber I → ℂ) (hw : ∀ J, ‖w J‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    Integrable (fun p => ∑' J : integralIdealClassFiber I,
      w J * mixedUnitOrbitMellinKernel K (idealElementRepresentative I J).1.1 s p)
        ((volume.restrict (Ioi 0)).prod (volume.restrict (mixedUnitLogDomain K))) := by
  let : Countable K := Finsupp.Countable.of_moduleFinite (R := ℚ)
  let : Countable Kˣ := Units.val_injective.countable
  let : Countable (nonzeroIdealElements I) := by
    change Countable {a : Kˣ // (a : K) ∈ (I : FractionalIdeal (𝓞 K)⁰ K)}
    infer_instance
  let : Countable (integralIdealClassFiber I) := (relativeElementClassMap_surjective I).countable
  have HM (J : integralIdealClassFiber I) :=
    (mixedUnitOrbitMellinKernel_measurable K (idealElementRepresentative I J).1.1 s).const_mul (w J)
  refine ⟨(Measurable.tsum HM).aestronglyMeasurable, ?_⟩
  change (∫⁻ p, ‖∑' J : integralIdealClassFiber I,
    w J * mixedUnitOrbitMellinKernel K (idealElementRepresentative I J).1.1 s p‖ₑ
      ∂(volume.restrict (Ioi 0)).prod (volume.restrict (mixedUnitLogDomain K))) < ⊤
  apply lt_of_le_of_lt (lintegral_mono (fun p => enorm_tsum_le_tsum_enorm))
  rw [lintegral_tsum (fun J => (HM J).enorm.aemeasurable)]
  exact lt_top_iff_ne_top.mpr
    (tsum_lintegral_weightedMixedUnitOrbitMellinKernel_ne_top K I w hw hs)

end
end ArtinMatthews.VaryingKummerAnalytic
