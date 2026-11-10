module

public import ArtinMatthews.GiantArrayRemoval
public import ArtinMatthews.MarkedCorrelationEndpoint
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The final ordered array-removal implication for the original fixed-
progression giant statistic. Each depth chooses its number of bands first;
the prime limit is then taken before the array count and depth limits.
The remaining hypothesis is explicitly the actual marked-prime bound. -/
namespace ArtinMatthews
noncomputable section
open Filter
open scoped Topology Asymptotics

theorem giant_fixed_progression_isLittleO_of_marked_prime_bounds
    {M : ℕ} (U : Finset (ZMod M)ˣ) (ε : ℝ) (hε : 0<ε) (hεq : ε<1/4)
    (Φ : ℝ → ℝ) {T a : ℝ} (hT : 0≤T) (ha : 0<a)
    (hΦ : Differentiable ℝ Φ) (hderiv : Continuous (deriv Φ)) (hΦT : Φ T=0)
    (hΦ0 : ∀ t, 0≤Φ t) (hlow : ∀ t<a, Φ t=0)
    (c A : ℝ) (n₀ : ℕ)
    (hmarked : ∀ n≥n₀, ∃ K : ℕ, ∀ e : Fin K → ℝ,
      (∀ i, (1/10 : ℝ)<e i ∧ e i<1/5) → Function.Injective e →
      ∀ δ : ℝ, 0<δ → ∀ᶠ x : ℝ in atTop,
        Real.log x / x * ‖giantFixedProgressionArrayPrimeSum U e ε Φ T x‖ ≤
          A * Real.exp (-(2*(n : ℝ))) /
            (markedCorrelationSieveExponent c (2*n))^2 + δ) :
    giantFixedProgressionPrimeSum U ε Φ T =o[atTop]
      (fun x : ℝ => x / Real.log x) := by
  have hzero : Φ 0=0 := hlow 0 ha
  have hF : ∀ᶠ x : ℝ in atTop, ∀ u, (u+1).Prime →
      ‖giantFixedResidueCenteredCoefficient U ε x u‖ ≤ 1 :=
    (giant_fixed_residue_coefficient_bound U hε hεq).mono (fun _ hx u _ => hx u)
  have hmarked' : ∀ n≥n₀, ∃ K : ℕ, ∀ e : Fin K → ℝ,
      (∀ i, (1/10 : ℝ)<e i ∧ e i<1/5) → Function.Injective e →
      ∀ δ : ℝ, 0<δ → ∀ᶠ x : ℝ in atTop,
        Real.log x / x * ‖markedPrimeSingleArrayCorrelation e Φ T
          (giantFixedResidueCenteredCoefficient U ε) x‖ ≤
          A * Real.exp (-(2*(n : ℝ))) /
            (markedCorrelationSieveExponent c (2*n))^2 + δ := by
    intro n hn
    obtain ⟨K,hK⟩ := hmarked n hn
    refine ⟨K,?_⟩
    intro e he hinj δ hδ
    filter_upwards [hK e he hinj δ hδ,
      giant_fixed_progression_array_eq_bounded U ε T hεq.le hT Φ hzero] with x hx heq
    rwa [heq e] at hx
  have h := marked_actual_correlation_isLittleO_of_marked Φ hT ha hΦ hderiv hΦT hΦ0 hlow
    (giantFixedResidueCenteredCoefficient U ε) (by norm_num : (0 : ℝ)≤1) hF c A n₀ hmarked'
  have heq : giantFixedProgressionPrimeSum U ε Φ T =ᶠ[atTop]
      markedPrimeCorrelation Φ T (giantFixedResidueCenteredCoefficient U ε) :=
    giant_fixed_progression_prime_eq_bounded U ε T hεq.le hT Φ hzero
  exact h.congr' heq.symm Filter.EventuallyEq.rfl

end
end ArtinMatthews
