module

public import ArtinMatthews.GiantSignedSourceVisitWeights
public import ArtinMatthews.GiantSignedConditioningEnergy
public import ArtinMatthews.GiantSignedTiltedLaw
public import ArtinMatthews.GiantSignedActualBoundary
public import ArtinMatthews.GiantSignedResidualBudget
public import ArtinMatthews.GiantSignedTiltBandBounds
public import ArtinMatthews.GiantSignedTiltedMass
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! The source schedule supplies the actual tilted law and bounded
empty-memory boundary uniformly at its growing even moment length. -/
namespace ArtinMatthews
open Filter
open scoped BigOperators ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

theorem giantSignedSourceTiltedBoundary_budget_eventually
    (q c C₀ : ℝ) (k ell : ℕ) (hM : 1 ≤ k+ell)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hc : 0 < c) (hC₀ : 0 ≤ C₀) :
    ∀ᶠ x : ℝ in atTop,
      ∀ (S B : Type*) [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
        (PS : S → Finset ℕ) (PB : B → Finset ℕ)
        [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val],
        (∀ j p, p ∈ PS j → p.Prime) → Pairwise (fun i j => Disjoint (PS i) (PS j)) →
        (∀ j, 0 < bandReciprocalMass (PS j)) → (∀ g, 0 < bandReciprocalMass (PB g)) →
        (∀ g (p : PB g), Real.exp ((Real.log x) ^ c) ≤ (p.val : ℝ)) →
        (Fintype.card B : ℝ) ≤ C₀ * Real.log (Real.log x) →
        let n := giantTwoSidedSourceMomentLength x
        let ν := fun g => giantSignedTiltedPrimeLaw (PB g) (giantSignedSourceVisitQ q n)
        (∀ g p, 0 ≤ ν g p) ∧
        (∀ g, (∑ p : PB g, ν g p) ≤ 2) ∧
        giantSignedStateEnergy PS ν (giantSignedBoundary (M := k+ell)) ≤ 2 := by
  have hb := Real.tendsto_log_atTop.eventually
    (giantSignedResidualBudget_eventually 1 c 0 C₀ 2 0 0 k ell zero_lt_one hc hC₀)
  filter_upwards [hb, Real.tendsto_log_atTop.eventually (eventually_ge_atTop (5 : ℝ))] with x hx hL
  intro S B _ _ _ _ PS PB _ hPS hdis hVS hVB hp hgroups
  let L := Real.log x
  let Pmin := Real.exp (L ^ c)
  let n := giantTwoSidedSourceMomentLength x
  let visitQ := giantSignedSourceVisitQ q n
  let ν := fun g => giantSignedTiltedPrimeLaw (PB g) visitQ
  have hL1 : 1 ≤ L := by dsimp [L]; linarith
  have hL0 : 0 ≤ L := zero_le_one.trans hL1
  have hn : ((n+1 : ℕ) : ℝ) ≤ L ^ (2 : ℝ) := by
    have hpow := Real.rpow_le_rpow_of_exponent_le hL1 (show (13/25 : ℝ) ≤ 1 by norm_num)
    rw [Real.rpow_one] at hpow
    have hlen := giantTwoSidedSourceMomentLength_le (x := x) hL1
    rw [Nat.cast_add, Nat.cast_one, Real.rpow_two]
    change (n : ℝ) ≤ 4 * L ^ (13/25 : ℝ) at hlen
    have hL5 : 5 ≤ L := hL
    nlinarith [mul_le_mul_of_nonneg_right hL5 hL0]
  obtain ⟨hlen, _, hdim, _⟩ := hx (Fintype.card B) (n+1) 0 hgroups hn (by simp)
  have hp0 : 0 < Pmin := Real.exp_pos _
  have hq0i (i : Fin (n+1)) : 0 ≤ visitQ i := (giantSignedSourceVisitQ_bounds hq0 hq1 n i).1
  have hq1i (i : Fin (n+1)) : visitQ i ≤ 1 := by
    have hs : Real.sqrt q ≤ 1 := by nlinarith [Real.sq_sqrt hq0, Real.sqrt_nonneg q]
    exact (giantSignedSourceVisitQ_bounds hq0 hq1 n i).2.trans hs
  change (∀ g p, 0 ≤ ν g p) ∧ (∀ g, (∑ p : PB g, ν g p) ≤ 2) ∧
    giantSignedStateEnergy PS ν (giantSignedBoundary (M := k+ell)) ≤ 2
  refine ⟨?_, ?_, ?_⟩
  · intro g p
    rw [show ν g p = markedHarmonicAtom (PB g) p * giantSignedPrimeDensity visitQ p.val
      from giantSignedTiltedPrimeLaw_eq (PB g) visitQ p]
    exact mul_nonneg (markedHarmonicAtom_nonneg (PB g) (hVB g))
      (zero_le_one.trans (giantSignedPrimeDensity_band_bounds visitQ hq0i hq1i Pmin hp0 (hp g p) hlen).1)
  · intro g
    have hb : 1 ≤ Fintype.card B := Nat.succ_le_of_lt (Fintype.card_pos_iff.mpr ⟨g⟩)
    have hbc : 1 ≤ ((Fintype.card B * (k+ell) : ℕ) : ℝ) := by
      exact_mod_cast (Nat.mul_le_mul hb hM)
    have hhalf : ((n+1 : ℕ) : ℝ) / Pmin ≤ 1/2 :=
      (le_mul_of_one_le_left (div_nonneg (Nat.cast_nonneg _) hp0.le) hbc).trans hdim
    exact giantSignedTiltedPrimeLaw_sum_le_two (PB g) visitQ (hVB g) hq0i hq1i Pmin hp0 (hp g) hhalf
  · rw [giantSignedStateEnergy_boundary PS]
    refine (giantSignedTiltedBoundary_energy_error PS hPS hdis hVS hVB visitQ hq0i hq1i
      Pmin hp0 hp hlen (k+ell) hdim).trans ?_
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num]
    exact ENNReal.ofReal_le_ofReal (by nlinarith [hdim])

end
end ArtinMatthews
