module

public import ArtinMatthews.MarkedMinorArcDirtyFresh
public import ArtinMatthews.MarkedTypeIIGoodSecond
public import ArtinMatthews.MarkedEstimateMertensBands
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

/-! The actual harmonic fresh-tuple probability and the tilted second-test failure. -/
noncomputable section
namespace ArtinMatthews

open Filter Set MeasureTheory
open scoped BigOperators Topology

abbrev MarkedFreshPrimeTuple {J : Type*} (e : J → ℝ) (x : ℝ) :=
  (j : J) → ↥(markedLogPowerBand (e j) x)

def markedFreshHarmonicLaw {J : Type*} [Fintype J] (e : J → ℝ) (x : ℝ)
    (t : MarkedFreshPrimeTuple e x) : ℝ :=
  finiteProductMass (fun j => markedHarmonicAtom (markedLogPowerBand (e j) x)) t

def markedFreshTiltedLaw {J : Type*} [Fintype J] (e : J → ℝ) (q x : ℝ)
    (t : MarkedFreshPrimeTuple e x) : ℝ :=
  finiteProductMass (fun j => markedTiltedBandAtom (markedLogPowerBand (e j) x)
    q (markedMemoryMomentLength x)) t

def markedFreshIntegerProduct {J : Type*} [Fintype J] (e : J → ℝ) (x : ℝ)
    (t : MarkedFreshPrimeTuple e x) : ℤ := ((∏ j, (t j:ℕ):ℕ):ℤ)

theorem markedFreshIntegerProduct_ne_zero {J : Type*} [Fintype J] (e : J → ℝ) (x : ℝ)
    (t : MarkedFreshPrimeTuple e x) : markedFreshIntegerProduct e x t ≠ 0 := by
  have hp : 0 < (∏ j, (t j:ℕ):ℕ) :=
    Finset.prod_pos (fun j _ => (mem_markedLogPowerBand.mp (t j).2).1.pos)
  unfold markedFreshIntegerProduct
  exact_mod_cast hp.ne'

theorem marked_actual_harmonic_fresh_probability_eventually {J : Type*}
    [Fintype J] [DecidableEq J] (e : J → ℝ) (he : ∀ j, 0 < e j) :
    ∀ᶠ x : ℝ in atTop,
      (∀ t, 0 ≤ markedFreshHarmonicLaw e x t) ∧ (∑ t, markedFreshHarmonicLaw e x t) = 1 := by
  have hV : ∀ᶠ x : ℝ in atTop, ∀ j, 0 < bandReciprocalMass (markedLogPowerBand (e j) x) :=
    eventually_all.mpr (fun j => (marked_log_power_band_mass_eventually (he j)).mono
      (fun _ hx => (by positivity : 0 < Real.log 2/2).trans hx.1))
  filter_upwards [hV] with x hV
  constructor
  · intro t
    exact Finset.prod_nonneg (fun j _ => markedHarmonicAtom_nonneg _ (hV j))
  · have hs (j : J) : (∑ p : ↥(markedLogPowerBand (e j) x),
        markedHarmonicAtom (markedLogPowerBand (e j) x) p) = 1 :=
      markedHarmonicAtom_sum _ (hV j)
    change (∑ t : MarkedFreshPrimeTuple e x, ∏ j,
      markedHarmonicAtom (markedLogPowerBand (e j) x) (t j)) = 1
    rw [← Fintype.prod_sum (fun j => markedHarmonicAtom (markedLogPowerBand (e j) x))]
    simp only [hs,Finset.prod_const_one]

theorem markedPairFailureProbability_eq_eventMass {Ω : Type*} [Fintype Ω]
    (Q : Finset ℤ) (T : Ω → ℤ) (w : Ω → ℝ) (ε : ℝ) (r : AddCircle (1:ℝ)) :
    markedPairFailureProbability Q T w ε r =
      markedEventMass w (fun t => r ∈ markedPairBadRoots Q (T t) ε) := by
  classical
  unfold markedPairFailureProbability markedEventMass
  apply Finset.sum_congr rfl
  intro t _
  split_ifs <;> simp

theorem marked_actual_fresh_failure_comparison_eventually {J : Type*}
    [Fintype J] [DecidableEq J] (e : J → ℝ) (he : ∀ j, (1/10:ℝ) ≤ e j) :
    ∀ᶠ x : ℝ in atTop, ∀ q : ℝ, 0 ≤ q → q ≤ 1 → ∀ (Q : Finset ℤ) (ε : ℝ) (r : AddCircle (1:ℝ)),
      markedPairFailureProbability Q (markedFreshIntegerProduct e x) (markedFreshTiltedLaw e q x) ε r ≤
        (2:ℝ)^(Fintype.card J)*
          markedPairFailureProbability Q (markedFreshIntegerProduct e x) (markedFreshHarmonicLaw e x) ε r := by
  filter_upwards [marked_actual_tilted_atom_comparison_eventually e he] with x hx
  intro q hq0 hq1 Q ε r
  rw [markedPairFailureProbability_eq_eventMass,markedPairFailureProbability_eq_eventMass]
  exact marked_fresh_event_mass_comparison _ _ (fun j p => (hx q hq0 hq1 j p).1)
    (fun j p => (hx q hq0 hq1 j p).2) _

/-- Off the literal harmonic second-test bad set, the actual tilted fresh
exceptional mass costs only the fixed factor 2^K. -/
theorem marked_actual_fresh_failure_off_good_eventually {J : Type*}
    [Fintype J] [DecidableEq J] (e : J → ℝ) (he : ∀ j, (1/10:ℝ) ≤ e j) (a : ℝ) :
    ∀ᶠ x : ℝ in atTop, ∀ q : ℝ, 0 ≤ q → q ≤ 1 → ∀ (Q : Finset ℤ) (r : AddCircle (1:ℝ)),
      r ∉ {r | Real.exp (-((Real.log x)^a)/4) ≤
        markedPairFailureProbability Q (markedFreshIntegerProduct e x) (markedFreshHarmonicLaw e x)
          (100*Real.exp (-((Real.log x)^a))) r} →
      markedPairFailureProbability Q (markedFreshIntegerProduct e x) (markedFreshTiltedLaw e q x)
        (100*Real.exp (-((Real.log x)^a))) r <
          (2:ℝ)^(Fintype.card J)*Real.exp (-((Real.log x)^a)/4) := by
  filter_upwards [marked_actual_fresh_failure_comparison_eventually e he] with x hx
  intro q hq0 hq1 Q r hgood
  have hg : markedPairFailureProbability Q (markedFreshIntegerProduct e x) (markedFreshHarmonicLaw e x)
      (100*Real.exp (-((Real.log x)^a))) r < Real.exp (-((Real.log x)^a)/4) :=
    lt_of_not_ge hgood
  exact (hx q hq0 hq1 Q _ r).trans_lt (mul_lt_mul_of_pos_left hg (by positivity))

end ArtinMatthews
