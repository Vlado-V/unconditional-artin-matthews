module

public import ArtinMatthews.VaryingKummerAnalyticMixedZeroScale
public import ArtinMatthews.VaryingKummerAnalyticZeroSeparation
public import ArtinMatthews.VaryingKummerAnalyticMixedNearOneZeros
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

/-! Actual varying-prime Kummer specialization of the general Dedekind
near-one zero estimates. This proves only the real-simple-unique possible
exceptional zero statement; it does not presume the paper's fixed-width
cyclotomic Hecke zero-free theorem. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Complex
open OAI.PrimeDegreePackets.AnalyticGrowth
open scoped Classical
noncomputable section

/-- The same universal constant controls the genuine Kummer completions and
all their possible near-one zeros, with explicit q² log q scale dependence. -/
theorem exists_uniform_primeKummer_nearOne :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℤ), a ≠ 0 → a ≠ 1 → a ≠ -1 →
      ∀ (q : ℕ), q.Prime → a.natAbs ≤ q →
      (2 ≤ mixedZeroScale (primeKummerField q a) C) ∧
      (mixedZeroScale (primeKummerField q a) C ≤
        (6+(2*C+2)/Real.log 2)*(q : ℝ)^2*Real.log q) ∧
      (∀ ρ : ℂ, mixedCompletedDedekindXi (primeKummerField q a) ρ = 0 →
        InNearOneBox (mixedZeroScale (primeKummerField q a) C) ρ →
        zeroMultiplicity (mixedCompletedDedekindXi (primeKummerField q a)) ρ = 1 ∧
          ρ.im = 0 ∧ ∀ τ, mixedCompletedDedekindXi (primeKummerField q a) τ = 0 →
            InNearOneBox (mixedZeroScale (primeKummerField q a) C) τ → τ = ρ) ∧
      (∀ h : ℝ, 0 < h → h ≤ 4/mixedZeroScale (primeKummerField q a) C →
        |(logDeriv (mixedCompletedDedekindXi (primeKummerField q a)) ((1+h : ℝ) : ℂ)).re -
          ∑' ρ, nearOneZeroPole (mixedCompletedDedekindXi (primeKummerField q a))
            (mixedZeroScale (primeKummerField q a) C) (1+h) ρ| ≤
          1014*(6+(2*C+2)/Real.log 2)*(q : ℝ)^2*Real.log q) := by
  obtain ⟨C,hC,hall⟩ := exists_uniform_mixedDedekind_nearOne.{0}
  refine ⟨C,hC,fun a ha0 ha1 ham1 q hq haq => ?_⟩
  have H := hall (primeKummerField q a)
  have hbound := primeKummerField_mixedZeroScale_le hC.le ha0 ha1 ham1 hq haq
  refine ⟨mixedZeroScale_two_le _ hC.le, hbound, H.1, ?_⟩
  intro h hh hh4
  exact (H.2 h hh hh4).trans (by nlinarith)

end
end ArtinMatthews.VaryingKummerAnalytic
