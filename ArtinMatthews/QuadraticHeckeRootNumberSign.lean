module

public import ArtinMatthews.VaryingKummerAnalyticMixedZetaContinuationBase
public import ArtinMatthews.VaryingKummerAnalyticMixedDedekindFunctionalEquation
public import ArtinMatthews.VaryingKummerAnalyticMixedXiBoundary
public import ArtinMatthews.VaryingKummerAnalyticMixedXiReality
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
open NumberField Complex Set Filter VaryingKummerAnalytic
open scoped NumberField Classical BigOperators Topology ComplexConjugate
noncomputable section

variable (K : Type) [Field K] [NumberField K]

theorem exists_mixedGammaFactor_positive_ofReal {t : ℝ} (ht : 0 < t) :
    ∃ x : ℝ, 0 < x ∧ mixedGammaFactor K t = (x : ℂ) := by
  let u (w : InfinitePlace K) : ℝ := (InfinitePlace.mult w : ℝ) * t / 2
  have hu (w : InfinitePlace K) : 0 < u w :=
    div_pos (mul_pos (Nat.cast_pos.mpr (InfinitePlace.mult_pos (w := w))) ht) (by norm_num)
  refine ⟨∏ w : InfinitePlace K, (1 / 2 : ℝ) * Real.pi ^ (-(u w)) * Real.Gamma (u w), ?_, ?_⟩
  · apply Finset.prod_pos
    intro w _
    exact mul_pos (mul_pos (by norm_num) (Real.rpow_pos_of_pos Real.pi_pos _))
      (Real.Gamma_pos_of_pos (hu w))
  · rw [mixedGammaFactor, Complex.ofReal_prod]
    apply Finset.prod_congr rfl
    intro w _
    have h : ((u w : ℝ) : ℂ) = (InfinitePlace.mult w : ℂ) * t / 2 := by dsimp [u]; push_cast; rfl
    rw [← h, Complex.Gamma_ofReal]
    simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat,
      Complex.ofReal_cpow Real.pi_pos.le, Complex.ofReal_neg]

private theorem mixedRegularizedDedekindZeta_positive_of_xi {t : ℝ} (ht : 0 < t)
    (hXi : 0 < (mixedCompletedDedekindXi K (t : ℂ)).re) :
    ∃ z : ℝ, 0 < z ∧ mixedRegularizedDedekindZeta K t = (z : ℂ) := by
  obtain ⟨g, hg, hG⟩ := exists_mixedGammaFactor_positive_ofReal K ht
  let x := (mixedCompletedDedekindXi K (t : ℂ)).re
  have hx : mixedCompletedDedekindXi K (t : ℂ) = (x : ℂ) := by
    have hc : conj (mixedCompletedDedekindXi K (t : ℂ)) =
        mixedCompletedDedekindXi K (t : ℂ) := by
      simpa only [Complex.conj_ofReal] using (mixedCompletedDedekindXi_conj K (t : ℂ)).symm
    exact (conj_eq_iff_re.mp hc).symm
  have hd : 0 < mixedDiscriminantScale K ^ t :=
    Real.rpow_pos_of_pos (mixedDiscriminantScale_pos K) _
  refine ⟨x * (mixedDiscriminantScale K ^ t)⁻¹ * g⁻¹ / t, by positivity, ?_⟩
  rw [mixedRegularizedDedekindZeta, hx, mixedInverseGammaFactor, hG,
    ← Complex.ofReal_cpow (mixedDiscriminantScale_pos K).le]
  push_cast
  rfl

theorem mixedRegularizedDedekindZeta_positive_near_zero_and_one :
    ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      (∃ z : ℝ, 0 < z ∧ mixedRegularizedDedekindZeta K (t : ℂ) = (z : ℂ)) ∧
      (∃ z : ℝ, 0 < z ∧ mixedRegularizedDedekindZeta K ((1 - t : ℝ) : ℂ) = (z : ℂ)) := by
  have hc : Continuous (fun t : ℝ => (mixedCompletedDedekindXi K (t : ℂ)).re) :=
    Complex.continuous_re.comp ((mixedCompletedDedekindXi_entire K).continuous.comp Complex.continuous_ofReal)
  have hpos : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), 0 < (mixedCompletedDedekindXi K (t : ℂ)).re :=
    hc.continuousAt.eventually (lt_mem_nhds (by
      simpa only [Complex.ofReal_zero] using mixedCompletedDedekindXi_zero_pos K))
  have hone : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), t < 1 := Iio_mem_nhds (by norm_num)
  filter_upwards [hpos.filter_mono inf_le_left, self_mem_nhdsWithin,
    hone.filter_mono inf_le_left] with t ht hzero hone
  refine ⟨mixedRegularizedDedekindZeta_positive_of_xi K hzero ht,
    mixedRegularizedDedekindZeta_positive_of_xi K (sub_pos.mpr hone) ?_⟩
  rw [Complex.ofReal_sub, Complex.ofReal_one, mixedCompletedDedekindXi_functional_equation,
    show (1 : ℂ) - (1 - t) = t by ring]
  exact ht

end
end ArtinMatthews
