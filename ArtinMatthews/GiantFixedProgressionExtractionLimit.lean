module

public import ArtinMatthews.GiantProgressionUncentered
public import ArtinMatthews.GiantMarkedCharacterCriterion
public import ArtinMatthews.GiantPrimeExtractionArithmetic
public import ArtinMatthews.GiantArrayOrderedLimit
public import ArtinMatthews.GiantFixedProgressionDepth
public import ArtinMatthews.GiantFixedProgressionExtraction
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! Actual rough sieve, prime extraction and array removal in the source
order of limits. At each sieve depth the marking depth is fixed before
the number of arrays or the large real parameter is chosen. -/
namespace ArtinMatthews
open Filter
open scoped Topology BigOperators Asymptotics
noncomputable section

theorem giant_fixed_progression_prime_isLittleO_of_actual_tuples {M : ℕ} [NeZero M]
    (U : Finset (ZMod M)ˣ) (ε : ℝ) (hε : 0<ε) (hεq : ε<1/4)
    (Φ : ℝ → ℝ) {a T : ℝ} (ha : 0<a) (hT : 0≤T)
    (hΦ : Differentiable ℝ Φ) (hderiv : Continuous (deriv Φ))
    (hsupp : Function.support Φ ⊆ Set.Ioo a T) (hΦ0 : ∀ t,0≤Φ t)
    (c : ℝ) (hc : 0<c) (hcε : c<ε/2)
    (htuple : ∀ m≥20000,∃ K : ℕ,∀ e : Fin K → ℝ,
      (∀ j,(1/10:ℝ)<e j ∧ e j<1/5) → Function.Injective e →
      ∀ (χ : DirichletCharacter ℂ M) j,j∈Finset.Icc 2 ⌈2/markedSieveExponent c m⌉₊ →
        giantOrdinaryTupleSum e χ (giantMarkedCenteredCore ε) Φ (T+1) (markedSieveExponent c m) j
          =o[atTop] (fun x : ℝ => x/Real.log x)) :
    giantFixedProgressionPrimeSum U ε Φ T =o[atTop] (fun x : ℝ => x/Real.log x) := by
  have hΦT : Φ T=0 := by
    by_contra h
    exact (lt_irrefl T) (hsupp h).2
  have hlow (t : ℝ) (ht : t<a) : Φ t=0 := by
    by_contra h
    exact (not_lt_of_ge ht.le) (hsupp h).1
  have hc1 : c≤1 := by linarith
  apply giant_fixed_progression_isLittleO_of_marked_prime_bounds U ε hε hεq Φ hT ha
    hΦ hderiv hΦT hΦ0 hlow c (giantFixedProgressionDepthConstant U Φ T) 20000
  intro n hn
  have hm : 20000≤4*n := by omega
  obtain ⟨K,hK⟩ := htuple (4*n) hm
  refine ⟨K,?_⟩
  intro e he hinj η hη
  filter_upwards [giant_fixed_progression_marked_prime_bound_of_tuple U e he hinj ε c (4*n)
    hε hεq hc hcε hm Φ ha hT hΦ hderiv hsupp hΦ0 (hK e he hinj) η hη] with x hx
  exact hx.trans (add_le_add (giantFixedProgression_depth_error_le U Φ T c hΦ0 hc hc1 n) le_rfl)

theorem giant_uncentered_prime_series_mean_of_actual_tuples {M : ℕ} [NeZero M]
    (U : Finset (ZMod M)ˣ) (ε : ℝ) (hε : 0<ε) (hεq : ε<1/4)
    (Φ : ℝ → ℝ) {a T : ℝ} (ha : 0<a) (haT : a≤T)
    (hΦ : Differentiable ℝ Φ) (hderiv : Continuous (deriv Φ)) (hcompact : HasCompactSupport Φ)
    (hsupp : Function.support Φ ⊆ Set.Ioo a T) (hΦ0 : ∀ t,0≤Φ t)
    (c : ℝ) (hc : 0<c) (hcε : c<ε/2)
    (htuple : ∀ m≥20000,∃ K : ℕ,∀ e : Fin K → ℝ,
      (∀ j,(1/10:ℝ)<e j ∧ e j<1/5) → Function.Injective e →
      ∀ (χ : DirichletCharacter ℂ M) j,j∈Finset.Icc 2 ⌈2/markedSieveExponent c m⌉₊ →
        giantOrdinaryTupleSum e χ (giantMarkedCenteredCore ε) Φ (T+1) (markedSieveExponent c m) j
          =o[atTop] (fun x : ℝ => x/Real.log x)) :
    Tendsto (fun x : ℝ => ((Real.log x/x:ℝ):ℂ)*giantUncenteredPrimeSeries U ε Φ x) atTop
      (𝓝 (((U.card:ℝ)/M.totient*giantPrimeConstant ε*∫ t : ℝ,Φ t:ℝ):ℂ)) := by
  exact giant_uncentered_prime_series_mean_of_centered U ε hε hεq Φ hΦ hderiv hcompact ha haT hsupp
    (giant_fixed_progression_prime_isLittleO_of_actual_tuples U ε hε hεq Φ ha
      (ha.le.trans haT) hΦ hderiv hsupp hΦ0 c hc hcε htuple)

end
end ArtinMatthews
