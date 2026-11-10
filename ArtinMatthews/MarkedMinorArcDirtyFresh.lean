module

public import ArtinMatthews.MarkedMinorArcProductMassActual
public import ArtinMatthews.MarkedTypeIIPadCollisions
public import ArtinMatthews.MarkedEstimateMertensBands
public import ArtinMatthews.MarkedTypeIICollisionDecay
public import Mathlib.NumberTheory.Chebyshev
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

/-! The literal tilted fresh-prime law is dominated by the harmonic law. -/
noncomputable section
namespace ArtinMatthews

open Filter
open scoped BigOperators Topology

def markedTiltedBandAtom (P : Finset ℕ) (q : ℝ) (N : ℕ) (p : ↥P) : ℝ :=
  markedMemoryPrimeAtom (bandReciprocalMass P) q N p.1

theorem markedTiltedBandAtom_le_two_harmonic (P : Finset ℕ) {q : ℝ} {N : ℕ}
    (hV : 0 < bandReciprocalMass P) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (p : ↥P)
    (hp : 0 < p.1) (hlarge : 2*(N+1) ≤ p.1+1) :
    markedTiltedBandAtom P q N p ≤ 2*markedHarmonicAtom P p := by
  have hpR : 0 < (p.1:ℝ) := by exact_mod_cast hp
  calc
    _ ≤ (2/bandReciprocalMass P)/(p.1:ℝ) :=
      (le_div_iff₀ hpR).mpr (markedMemoryPrimeAtom_mul_prime_le hV hq0 hq1 hlarge)
    _ = _ := by unfold markedHarmonicAtom; ring

theorem marked_actual_tilted_atom_comparison_eventually {J : Type*} [Fintype J]
    (e : J → ℝ) (he : ∀ j, (1/10:ℝ) ≤ e j) :
    ∀ᶠ x : ℝ in atTop, ∀ q : ℝ, 0 ≤ q → q ≤ 1 → ∀ j,
      ∀ p : ↥(markedLogPowerBand (e j) x),
        0 ≤ markedTiltedBandAtom (markedLogPowerBand (e j) x) q (markedMemoryMomentLength x) p ∧
        markedTiltedBandAtom (markedLogPowerBand (e j) x) q (markedMemoryMomentLength x) p ≤
          2*markedHarmonicAtom (markedLogPowerBand (e j) x) p := by
  have hV : ∀ᶠ x : ℝ in atTop, ∀ j,
      Real.log 2/2 ≤ bandReciprocalMass (markedLogPowerBand (e j) x) :=
    eventually_all.mpr (fun j => (marked_log_power_band_mass_eventually
      (show 0 < e j by linarith [he j])).mono (fun _ hx => hx.1.le))
  filter_upwards [hV,markedMemoryMomentLength_prime_small_eventually,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with x hV hN hlog
  intro q hq0 hq1 j p
  have hVp : 0 < bandReciprocalMass (markedLogPowerBand (e j) x) :=
    (by positivity : 0 < Real.log 2/2).trans_le (hV j)
  have hlarge := hN p.1 (marked_band_common_lower (he j) hlog p.2)
  exact ⟨(markedMemoryPrimeAtom_pos hVp hq0 hq1 hlarge).le,
    markedTiltedBandAtom_le_two_harmonic _ hVp hq0 hq1 p
      (mem_markedLogPowerBand.mp p.2).1.pos hlarge⟩

theorem marked_fresh_product_mass_comparison {J : Type*} [Fintype J]
    {Ω : J → Type*} (ν μ : ∀ j, Ω j → ℝ)
    (hν : ∀ j p, 0 ≤ ν j p) (hcomp : ∀ j p, ν j p ≤ 2*μ j p) (t : ∀ j, Ω j) :
    finiteProductMass ν t ≤ (2:ℝ)^(Fintype.card J)*finiteProductMass μ t := by
  calc
    _ ≤ ∏ j, 2*μ j (t j) := Finset.prod_le_prod₀ (fun j _ => hν j _) (fun j _ => hcomp j _)
    _ = _ := by rw [Finset.prod_mul_distrib]; simp only [Finset.prod_const,Finset.card_univ,finiteProductMass]

theorem marked_fresh_event_mass_comparison {J : Type*} [Fintype J] [DecidableEq J]
    {Ω : J → Type*} [∀ j, Fintype (Ω j)] (ν μ : ∀ j, Ω j → ℝ)
    (hν : ∀ j p, 0 ≤ ν j p) (hcomp : ∀ j p, ν j p ≤ 2*μ j p)
    (E : (∀ j, Ω j) → Prop) :
    markedEventMass (finiteProductMass ν) E ≤
      (2:ℝ)^(Fintype.card J)*markedEventMass (finiteProductMass μ) E := by
  classical
  unfold markedEventMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t _
  by_cases ht : E t
  · simp only [ht,ite_true,one_mul]
    exact marked_fresh_product_mass_comparison ν μ hν hcomp t
  · simp only [ht,ite_false,zero_mul,mul_zero]
    exact le_rfl

/-- The comparison holds uniformly for every subset of the actual fresh
groups and every actual exceptional tuple set, using the literal μ and ν. -/
theorem marked_actual_fresh_subset_event_comparison_eventually {J : Type*}
    [Fintype J] [DecidableEq J] (e : J → ℝ) (he : ∀ j, (1/10:ℝ) ≤ e j) :
    ∀ᶠ x : ℝ in atTop, ∀ (I : Finset J) (q : ℝ), 0 ≤ q → q ≤ 1 →
      ∀ E : ((j : ↥I) → ↥(markedLogPowerBand (e j.1) x)) → Prop,
        markedEventMass (finiteProductMass (fun j : ↥I =>
          markedTiltedBandAtom (markedLogPowerBand (e j.1) x) q (markedMemoryMomentLength x))) E ≤
        (2:ℝ)^I.card*markedEventMass (finiteProductMass (fun j : ↥I =>
          markedHarmonicAtom (markedLogPowerBand (e j.1) x))) E := by
  filter_upwards [marked_actual_tilted_atom_comparison_eventually e he] with x hx
  intro I q hq0 hq1 E
  simpa only [Fintype.card_coe] using marked_fresh_event_mass_comparison
    (fun j : ↥I => markedTiltedBandAtom (markedLogPowerBand (e j.1) x) q (markedMemoryMomentLength x))
    (fun j : ↥I => markedHarmonicAtom (markedLogPowerBand (e j.1) x))
    (fun j p => (hx q hq0 hq1 j.1 p).1) (fun j p => (hx q hq0 hq1 j.1 p).2) E

end ArtinMatthews
