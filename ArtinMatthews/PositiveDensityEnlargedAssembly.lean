module

public import ArtinMatthews.PositiveDensityCandidateWeights
public import ArtinMatthews.KummerSplittingDiscriminantBasis
public import ArtinMatthews.PositiveDensityCandidateCRT
public import ArtinMatthews.VaryingKummerAnalyticMixedDedekindCompletion
public import ArtinMatthews.PositiveDensityAssembly
public import ArtinMatthews.PositiveDensityEnlargedCutoff
public import ArtinMatthews.PositiveDensitySmallIndexActual
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

/-! The integer sieve cutoff is chosen using the uniform splitting
constant before the normalized mean for that fixed progression is used. -/

noncomputable section
namespace ArtinMatthews

open Filter VaryingKummerAnalytic
open scoped BigOperators Topology

theorem positiveDyadicLowerBound_of_enlarged_mean
    {S : Finset ℤ} (hS : AdmissibleBases S) {δ ε : ℝ}
    (hδ : δ ≤ 1) (hεδ : ε < δ) (hε : 0 < ε) (hεq : ε < 1 / 4)
    (hzero : ∀ a ∈ S, ∀ q : ℕ, q.Prime → 2 < q → a.natAbs ≤ q →
      ∀ ρ : ℂ, mixedCompletedDedekindXi (primeKummerField q a) ρ = 0 → ρ.re ≤ 1 - δ)
    {u r₃ : ℕ} (hprog : IsQuadraticProgressionFor S u r₃) (select : ℕ → Prop)
    (hselect : ∀ p, select p → r₃ = 2 ∨ ∀ a ∈ S, ¬ IsCubeMod p a)
    (Φ : ℝ → ℝ) (hΦ : ∀ t, 0 ≤ Φ t ∧ Φ t ≤ 1)
    {T : ℝ} (hT₁ : 1 < T) (hT₂ : T < 2) (hs : Function.support Φ ⊆ Set.Ioo 1 T)
    {κ : ℝ} (hκ : 0 < κ)
    (hmean : ∀ Y : ℕ, 3 ≤ Y → (∀ a ∈ S, a.natAbs ≤ Y) →
      let M := enlargedModulus (quadraticModulus S) (giantSieveNewPrimes S Y)
      let U := giantSieveEnlargedUnits hprog Y
      Tendsto (fun x : ℝ => ((Real.log x / x : ℝ) : ℂ) *
        giantSelectedPrimeTest U select ε Φ T x) atTop
        (𝓝 (((U.card : ℝ) / Nat.totient M * κ : ℝ) : ℂ))) :
    PositiveDyadicLowerBound S := by
  obtain ⟨C, hC, hsmall⟩ := giantSieve_enlarged_smallIndex_bound_of_zero_region hS hδ hεδ hzero
  have hB : 0 ≤ C * (S.card : ℝ) := mul_nonneg hC.le (Nat.cast_nonneg _)
  obtain ⟨Y, hY, habs, hgap⟩ := giantSieve_exists_enlarged_cutoff hprog hB
    (by positivity : 0 < κ / 4)
  let M := enlargedModulus (quadraticModulus S) (giantSieveNewPrimes S Y)
  let U := giantSieveEnlargedUnits hprog Y
  let κY := (U.card : ℝ) / Nat.totient M * κ
  let b := C * (S.card : ℝ) / (Y : ℝ)
  have hgap' : b < κY / 4 := by
    calc
      b < (κ / 4) * ((U.card : ℝ) / Nat.totient M) := hgap
      _ = κY / 4 := by dsimp only [κY]; ring
  have hb : 0 ≤ b := div_nonneg hB (Nat.cast_nonneg _)
  have hκY : 0 < κY := by linarith
  have hbc : b < κY / 2 := by linarith
  let P := giantSieveCandidates U select ε Φ T
  let w := giantSieveWeight Φ
  let error := fun x : ℝ => 4 * C * (S.card : ℝ) * x ^ (1 - δ + ε)
  obtain ⟨herr, hbad⟩ := hsmall Y hY habs u r₃ hprog select hselect Φ hΦ T hT₁ hT₂ hs
  have hstruct := giantSieveCandidates_structural_eventually hS U select ε Φ hΦ hT₁ hT₂ hs
  have hcount := giantSieveCandidates_weighted_lower_of_mean U select Φ
    (by linarith) hT₂.le hεq.le hκY (hmean Y hY habs)
  exact positiveDyadicLowerBound_of_weighted_sieve_inputs hS hε (by linarith)
    (half_pos hκY) hbc P w error
    (hstruct.mono fun _ h p hp => (h p hp).1)
    (hstruct.mono fun _ h p hp => (h p hp).2.1)
    (hstruct.mono fun _ h p hp => (h p hp).2.2.1)
    (hstruct.mono fun _ h p hp => (h p hp).2.2.2.1)
    (hstruct.mono fun _ h p hp => (h p hp).2.2.2.2)
    hcount hbad herr

end ArtinMatthews
