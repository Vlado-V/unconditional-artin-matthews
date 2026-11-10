module

public import ArtinMatthews.Index
public import ArtinMatthews.KummerCyclotomicTower
public import ArtinMatthews.PrincipalDedekindSourceSignal
public import ArtinMatthews.VaryingKummerAnalyticPrimitiveGaussianSignal
public import ArtinMatthews.VaryingKummerAnalyticRayIdealInverse
public import GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.Basic
public import ArtinMatthews.KummerGaussianZeroRegion
public import ArtinMatthews.VaryingKummerAnalyticKummerSplitEstimate
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
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

/-! The unrestricted-q splitting conclusion from the exact remaining
Gaussian power bounds. The count constant is chosen before q, a and the
two per-field/per-character Big-O hypotheses. No uniform Big-O constant
or onset is required by this reduction. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Filter Asymptotics
open OAI.SevenEighths.FiniteFourier
open scoped NumberField Classical Topology
noncomputable section

theorem exists_primeKummer_split_count_of_gaussian_power_bounds :
    ∃ C : ℝ,0 < C ∧ ∀ (q : ℕ) (a : ℤ) [NeZero q] [NeZero a],
      a ≠ 1 → a ≠ -1 → q.Prime → 2 < q → a.natAbs ≤ q →
      ∀ (β c : ℝ),0 ≤ β → β < 2 →
      (principalSourceGaussianSignal (twelfthCyclotomicField q) c =O[atTop]
        (fun Z : ℝ => Z^(β+c))) →
      (∀ (f : Ideal (𝓞 (twelfthCyclotomicField q))) (hf : f ≠ ⊥)
        (ψ : EvenIdealRayCharacter (twelfthCyclotomicField q) f)
        (hprim : IsPrimitiveOnIdeals ψ.residue), ψ.IsNonprincipal →
        ψ.coefficient ≠ ψ.inverse.coefficient →
        Real.log (f.absNorm : ℝ) ≤ (12*q:ℝ)*((72*(q:ℝ)^2+2)*Real.log (12*q)) →
        ψ.primitiveGaussianSignal hf hprim c =O[atTop] (fun Z : ℝ => Z^(β+c))) →
      ∀ (x : ℝ) (S : Finset Nat.Primes),1 < x →
        (∀ p ∈ S,x ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2*x ∧
          ¬ (p.val : ℤ) ∣ (q : ℤ) ∧ (a : ZMod p.val) ≠ 0 ∧ q ∣ multiplicativeIndex p a) →
        (S.card : ℝ) ≤ C*(x/((q : ℝ)*((q : ℝ)-1)*Real.log x)+
          x^β*Real.log (2*(q : ℝ))/Real.log x) := by
  obtain ⟨C,hC,hbound⟩ := exists_primeKummer_split_count_bound_of_zero_region
  refine ⟨C,hC,?_⟩
  intro q a _ _ ha1 ham1 hprime hq haq β c hβ hβ2 hprincipal hprimitive x S hx hS
  exact hbound a (NeZero.ne a) ha1 ham1 q hprime haq x β S hx hβ
    (primeKummer_zero_region_of_gaussian_power_bounds q a hprime hq haq
      β c hβ hβ2 hprincipal hprimitive) hS

end
end ArtinMatthews.VaryingKummerAnalytic
