module

public import ArtinMatthews.KummerCyclotomicTower
public import ArtinMatthews.KummerSplittingDiscriminantBasis
public import ArtinMatthews.PrincipalDedekindSourceSignal
public import ArtinMatthews.VaryingKummerAnalyticPrimitiveGaussianSignal
public import ArtinMatthews.VaryingKummerAnalyticRayIdealInverse
public import ArtinMatthews.KummerPrimitiveZeroSources
public import ArtinMatthews.PrincipalDedekindSourceMellin
public import ArtinMatthews.VaryingKummerAnalyticPrimitiveGaussianMellin
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

/-! Exact analytic input for the varying-q Kummer zero region. The
Big-O constants and starting points are allowed to depend on the field
and character. Only the exponent beta is shared. No power bound is
proved or assumed implicitly by a definition. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Filter Asymptotics
open OAI.SevenEighths.FiniteFourier
open scoped NumberField Classical Topology
noncomputable section

theorem primeKummer_zero_region_of_gaussian_power_bounds
    (q : ℕ) (a : ℤ) [NeZero q] [NeZero a]
    (hprime : q.Prime) (hq : 2 < q) (haq : a.natAbs ≤ q)
    (β c : ℝ) (hβ : 0 ≤ β) (hβ2 : β < 2)
    (hprincipal : principalSourceGaussianSignal (twelfthCyclotomicField q) c =O[atTop]
      (fun Z : ℝ => Z^(β+c)))
    (hprimitive : ∀ (f : Ideal (𝓞 (twelfthCyclotomicField q))) (hf : f ≠ ⊥)
      (ψ : EvenIdealRayCharacter (twelfthCyclotomicField q) f)
      (hprim : IsPrimitiveOnIdeals ψ.residue), ψ.IsNonprincipal →
      ψ.coefficient ≠ ψ.inverse.coefficient →
      Real.log (f.absNorm : ℝ) ≤ (12*q:ℝ)*((72*(q:ℝ)^2+2)*Real.log (12*q)) →
      ψ.primitiveGaussianSignal hf hprim c =O[atTop] (fun Z : ℝ => Z^(β+c))) :
    ∀ s : ℂ,mixedCompletedDedekindXi (primeKummerField q a) s = 0 → s.re ≤ β := by
  intro s hz
  by_contra hs
  have hsr : β < s.re := lt_of_not_ge hs
  have hspos : 0 < s.re := lt_of_le_of_lt hβ hsr
  rcases primeKummer_prime_xi_zero_sources q a hprime hq haq hspos hz with
    hbase | ⟨w,hnonreal,_,hconductor⟩
  · have hn := principalDedekindRegularized_ne_zero_of_sourceGaussianSignal_power_bound
      (twelfthCyclotomicField q) c β hβ2 hprincipal hsr
    apply hn
    change mixedDedekindEntireNumerator (twelfthCyclotomicField q) s = 0
    rw [mixedDedekindEntireNumerator_eq_regularized _ (by
      intro he
      simp only [he,Complex.zero_re,lt_self_iff_false] at hspos)]
    exact hbase
  · exact (w.primitiveCharacter.primitiveContinued_ne_zero_of_gaussianSignal_power_bound
      w.conductor_ne_zero w.primitive w.nonprincipal c β hβ2
      (hprimitive w.conductor w.conductor_ne_zero w.primitiveCharacter w.primitive
        w.nonprincipal hnonreal hconductor) hsr) w.zero

end
end ArtinMatthews.VaryingKummerAnalytic
