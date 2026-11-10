module

public import ArtinMatthews.MarkedMinorArcProductMass
public import ArtinMatthews.DivisorWeights
public import ArtinMatthews.MarkedEstimateMertensBandCore
public import ArtinMatthews.MarkedBonferroniTail
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

/-! Actual moment length and prime-band normalizers discharge PD's product-mass hypotheses. -/
noncomputable section
namespace ArtinMatthews

open Filter
open scoped BigOperators Topology

/-- PD03: R=ceil(sqrt(log x)/2), N=2R. -/
def markedMemoryMomentLength (x : ℝ) : ℕ :=
  2*⌈(Real.log x)^(1/2:ℝ)/2⌉₊

theorem markedMemoryMomentLength_prime_small_eventually :
    ∀ᶠ x : ℝ in atTop, ∀ p : ℕ,
      Real.exp ((Real.log x)^(1/10:ℝ)) ≤ (p:ℝ) →
        2*(markedMemoryMomentLength x+1) ≤ p+1 := by
  have h1 := rpow_mul_exp_neg_rpow_tendsto (1/2:ℝ)
    (by norm_num : (0:ℝ) < 1/10) (by norm_num : (0:ℝ) < 1)
  have h0 := rpow_mul_exp_neg_rpow_tendsto (0:ℝ)
    (by norm_num : (0:ℝ) < 1/10) (by norm_num : (0:ℝ) < 1)
  have hl : Tendsto (fun L : ℝ => (2*L^(1/2:ℝ)+6)*Real.exp (-L^(1/10:ℝ)))
      atTop (nhds 0) := by
    convert (h1.const_mul 2).add (h0.const_mul 6) using 1
    · ext L
      simp only [neg_mul, one_mul, Real.rpow_zero]
      ring
    · norm_num
  filter_upwards [(hl.comp Real.tendsto_log_atTop).eventually (Iio_mem_nhds (by norm_num : (0:ℝ)<1)),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with x hx hlog
  intro p hp
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ (Real.log x)^(1/2:ℝ)/2 from
    div_nonneg (Real.rpow_nonneg (by linarith) _) (by norm_num))
  have hN : (markedMemoryMomentLength x:ℝ) ≤ (Real.log x)^(1/2:ℝ)+2 := by
    unfold markedMemoryMomentLength
    push_cast
    linarith
  have hexp : 2*(Real.log x)^(1/2:ℝ)+6 < Real.exp ((Real.log x)^(1/10:ℝ)) := by
    have hh : (2*(Real.log x)^(1/2:ℝ)+6)/Real.exp ((Real.log x)^(1/10:ℝ)) < 1 := by
      simpa only [Function.comp_def, Real.exp_neg, div_eq_mul_inv] using hx
    simpa only [one_mul] using (div_lt_iff₀ (Real.exp_pos _)).mp hh
  have hn : 2*((markedMemoryMomentLength x:ℝ)+1) ≤ (p:ℝ)+1 := by linarith
  exact_mod_cast hn

def markedActualMemoryProductMass {J : Type*} [Fintype J] (e : J → ℝ)
    (q x : ℝ) (p : J → ℕ) : ℝ :=
  markedMemoryProductMass (fun j => bandReciprocalMass (markedLogPowerBand (e j) x))
    q (markedMemoryMomentLength x) p

/-- The constant depends only on the number of groups. The band exponents
affect only the eventual threshold. -/
theorem marked_actual_memory_product_mass_eventually {J : Type*} [Fintype J]
    (e : J → ℝ) (he : ∀ j, (1/10:ℝ) ≤ e j) :
    ∀ᶠ x : ℝ in atTop, ∀ (q Y : ℝ) (p : J → ℕ),
      0 ≤ q → q ≤ 1 → 0 < Y →
      (∀ j, p j ∈ markedLogPowerBand (e j) x) →
      Y ≤ ((∏ j, p j : ℕ):ℝ) →
      markedActualMemoryProductMass e q x p ≤ (4/Real.log 2)^(Fintype.card J)/Y := by
  have hV : ∀ᶠ x : ℝ in atTop, ∀ j,
      Real.log 2/2 ≤ bandReciprocalMass (markedLogPowerBand (e j) x) :=
    eventually_all.mpr (fun j => (marked_log_power_band_mass_eventually
      (show 0 < e j by linarith [he j])).mono (fun _ hx => hx.1.le))
  filter_upwards [hV, markedMemoryMomentLength_prime_small_eventually,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with x hV hN hlog
  intro q Y p hq0 hq1 hY hp hYp
  have hprime (j : J) : (p j).Prime := (mem_markedLogPowerBand.mp (hp j)).1
  have hlarge (j : J) : 2*(markedMemoryMomentLength x+1) ≤ p j+1 :=
    hN (p j) (marked_band_common_lower (he j) hlog (hp j))
  have hh := (markedMemoryProductMass_le_reciprocal
    (by positivity : 0 < Real.log 2/2) hV hq0 hq1 p (fun j => (hprime j).pos) hlarge).trans
    (div_le_div_of_nonneg_left (by positivity) hY hYp)
  simpa only [markedActualMemoryProductMass, show 2/(Real.log 2/2) = 4/Real.log 2 by ring] using hh

theorem marked_actual_memory_product_mass_cutoff_eventually {J : Type*} [Fintype J]
    (e : J → ℝ) (he : ∀ j, (1/10:ℝ) ≤ e j) (η : ℝ → ℂ)
    (hη : Function.support η ⊆ Set.Icc 1 4) :
    ∀ᶠ x : ℝ in atTop, ∀ (q Y : ℝ) (p : J → ℕ),
      0 ≤ q → q ≤ 1 → 0 < Y →
      (∀ j, p j ∈ markedLogPowerBand (e j) x) →
      η (((∏ j, p j : ℕ):ℝ)/Y) ≠ 0 →
      markedActualMemoryProductMass e q x p ≤ (4/Real.log 2)^(Fintype.card J)/Y := by
  filter_upwards [marked_actual_memory_product_mass_eventually e he] with x hx
  intro q Y p hq0 hq1 hY hp hcut
  have hb : Y ≤ ((∏ j, p j : ℕ):ℝ) := by
    have hh : 1 ≤ ((∏ j, p j : ℕ):ℝ)/Y := (hη hcut).1
    simpa only [one_mul] using (le_div_iff₀ hY).mp hh
  exact hx q Y p hq0 hq1 hY hp hb

end ArtinMatthews
