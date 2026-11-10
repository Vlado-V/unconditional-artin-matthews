module

public import ArtinMatthews.VaryingKummerAnalyticMixedDedekindCompletion
public import ArtinMatthews.VaryingKummerAnalyticMixedGammaAnalytic
public import ArtinMatthews.VaryingKummerAnalyticMixedMellinFubini
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Convex.Contractible
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

/-! Conjugation symmetry of the actual arbitrary-signature completion, proved
from its real convergent ideal series and entire analytic uniqueness. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Set
open scoped NumberField nonZeroDivisors Classical BigOperators ComplexConjugate
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem mixedIdealUnitXi_conj_ofReal (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {r : ℝ} (hr : 1 < r) :
    conj (mixedIdealUnitXi K I (r : ℂ)) = mixedIdealUnitXi K I (r : ℂ) := by
  rw [mixedIdealUnitXi_real_eq_partial K I r hr]
  simp only [map_mul, map_div₀, map_sub, Complex.conj_natCast, Complex.conj_ofReal, map_ofNat]

theorem mixedCompletedDedekindXi_conj_ofReal {r : ℝ} (hr : 1 < r) :
    conj (mixedCompletedDedekindXi K (r : ℂ)) = mixedCompletedDedekindXi K (r : ℂ) := by
  have hp (a : ℝ) (ha : 0 < a) : conj ((a : ℂ)^(r : ℂ)) = (a : ℂ)^(r : ℂ) := by
    rw [← Complex.ofReal_cpow ha.le]
    exact Complex.conj_ofReal _
  unfold mixedCompletedDedekindXi
  simp only [map_mul, map_inv₀, Complex.conj_ofReal, map_sum,
    hp _ (mixedDiscriminantScale_pos K),
    hp _ (fractionalIdeal_absNorm_pos _), mixedIdealUnitXi_conj_ofReal K _ hr]

/-- The actual Dedekind completion is of real type. -/
theorem mixedCompletedDedekindXi_conj (s : ℂ) :
    mixedCompletedDedekindXi K (conj s) = conj (mixedCompletedDedekindXi K s) := by
  let f := mixedCompletedDedekindXi K
  have hf : Differentiable ℂ f := mixedCompletedDedekindXi_entire K
  have hg : Differentiable ℂ (fun z => conj (f (conj z))) := by
    intro z
    simpa only [Function.comp_def, starRingEnd_self_apply] using (hf (conj z)).conj_conj
  have he := halfPlane_eq_of_real_eq hf.differentiableOn hg.differentiableOn
    (fun r hr => by
      rw [Complex.conj_ofReal]
      exact (mixedCompletedDedekindXi_conj_ofReal K hr).symm)
  have hall := (hf.differentiableOn.analyticOnNhd isOpen_univ).eq_of_eventuallyEq
    (hg.differentiableOn.analyticOnNhd isOpen_univ) (z₀ := (2 : ℂ)) (by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (show 1 < (2 : ℂ).re by norm_num)] with z hz
      exact he hz)
  have H := congrFun hall (conj s)
  simpa only [starRingEnd_self_apply] using H

end
end ArtinMatthews.VaryingKummerAnalytic
