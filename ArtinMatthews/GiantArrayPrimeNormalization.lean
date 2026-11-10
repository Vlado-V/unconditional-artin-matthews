module

public import ArtinMatthews.GiantActualRoughSieve
public import ArtinMatthews.GiantArrayRemoval
public import ArtinMatthews.GiantArrayOrderedLimit
public import ArtinMatthews.MarkedCorrelationMeanScale
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Exact model-mean normalization at the ordinary prime-extraction output.
The input is the actual unnormalized single-array prime sum and the true
independent divisor-model mean, as in the rough-sieve limit. -/
namespace ArtinMatthews
noncomputable section
open Filter
open scoped BigOperators Topology Asymptotics

def giantFixedProgressionWeightedPrimeSum {M : ℕ} (U : Finset (ZMod M)ˣ)
    {I : Type*} [Fintype I] (e : I → ℝ) (ε : ℝ) (Φ : ℝ → ℝ) (T x : ℝ) : ℂ :=
  ∑ u ∈ (Finset.Icc 0 ⌊T*x⌋₊).filter (fun u => (u+1).Prime),
    (Φ ((u : ℝ)/x) : ℂ) * giantFixedResidueLiteralCoefficient U ε x u *
      (literalMarkedArrayWeight e x u : ℂ)

theorem giant_fixed_progression_array_mean_eq {M : ℕ} (U : Finset (ZMod M)ˣ)
    {I : Type*} [Fintype I] [DecidableEq I] (e : I → ℝ)
    (ε : ℝ) (Φ : ℝ → ℝ) (T x : ℝ) :
    giantFixedProgressionArrayPrimeSum U e ε Φ T x =
      giantFixedProgressionWeightedPrimeSum U e ε Φ T x / (literalMarkedArrayMean e x : ℂ) := by
  exact marked_normalized_sum_eq
    ((Finset.Icc 0 ⌊T*x⌋₊).filter (fun u => (u+1).Prime))
    (fun u => (Φ ((u : ℝ)/x) : ℂ) * giantFixedResidueLiteralCoefficient U ε x u)
    (literalMarkedArrayWeight e x) (literalMarkedArrayMean e x)

theorem giant_fixed_progression_array_mean_scale {M : ℕ} (U : Finset (ZMod M)ˣ)
    {I : Type*} [Fintype I] [DecidableEq I] (e : I → ℝ)
    (ε : ℝ) (Φ : ℝ → ℝ) (T x : ℝ) (hm : 0≤literalMarkedArrayMean e x) :
    Real.log x / x * ‖giantFixedProgressionArrayPrimeSum U e ε Φ T x‖ =
      Real.log x / (x*literalMarkedArrayMean e x) *
        ‖giantFixedProgressionWeightedPrimeSum U e ε Φ T x‖ := by
  rw [giant_fixed_progression_array_mean_eq, norm_div, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hm]
  ring

/-- The final array-removal endpoint accepts the actual output normalization
of the rough-prime replacement step, with no model-mean substitution. -/
theorem giant_fixed_progression_isLittleO_of_raw_marked_prime_bounds
    {M : ℕ} (U : Finset (ZMod M)ˣ) (ε : ℝ) (hε : 0<ε) (hεq : ε<1/4)
    (Φ : ℝ → ℝ) {T a : ℝ} (hT : 0≤T) (ha : 0<a)
    (hΦ : Differentiable ℝ Φ) (hderiv : Continuous (deriv Φ)) (hΦT : Φ T=0)
    (hΦ0 : ∀ t, 0≤Φ t) (hlow : ∀ t<a, Φ t=0)
    (c A : ℝ) (n₀ : ℕ)
    (hmarked : ∀ n≥n₀, ∃ K : ℕ, ∀ e : Fin K → ℝ,
      (∀ i, (1/10 : ℝ)<e i ∧ e i<1/5) → Function.Injective e →
      ∀ δ : ℝ, 0<δ → ∀ᶠ x : ℝ in atTop,
        Real.log x / (x*literalMarkedArrayMean e x) *
          ‖giantFixedProgressionWeightedPrimeSum U e ε Φ T x‖ ≤
          A * Real.exp (-(2*(n : ℝ))) /
            (markedCorrelationSieveExponent c (2*n))^2 + δ) :
    giantFixedProgressionPrimeSum U ε Φ T =o[atTop]
      (fun x : ℝ => x / Real.log x) := by
  apply giant_fixed_progression_isLittleO_of_marked_prime_bounds U ε hε hεq
    Φ hT ha hΦ hderiv hΦT hΦ0 hlow c A n₀
  intro n hn
  obtain ⟨K,hK⟩ := hmarked n hn
  refine ⟨K,?_⟩
  intro e he hinj δ hδ
  filter_upwards [hK e he hinj δ hδ,
    literalMarkedArrayMean_lower_eventually e (fun i => lt_trans (by norm_num) (he i).1)]
    with x hx hmean
  rw [giant_fixed_progression_array_mean_scale U e ε Φ T x
    ((by positivity : (0 : ℝ)≤(1/2 : ℝ)^Fintype.card (Fin K)).trans hmean)]
  exact hx

end
end ArtinMatthews
