module

public import ArtinMatthews.MarkedMemorySourceTilt
public import ArtinMatthews.MarkedEstimateMertensBands
public import ArtinMatthews.MarkedTypeIICollisionDecay
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Actual one-line birth atoms have uniformly bounded total band mass.
The baseline lower bound and the existing finite-band reciprocal-mass
theorem are used explicitly; no probability normalization is assumed. -/
namespace ArtinMatthews
noncomputable section
open Filter
open scoped BigOperators Topology
attribute [local instance] Classical.decEq Classical.propDecidable

theorem markedMemoryLineBirthAtom_bounds {q : ℝ} (hq0 : 0≤q) (hq1 : q≤1)
    {n : ℕ} (p : Nat.Primes) (hlarge : 2*(n+1)≤(p:ℕ)+1) :
    0 < markedMemoryLineBirthAtom q n p ∧
      markedMemoryLineBirthAtom q n p≤2/(p:ℝ) ∧ markedMemoryLineBirthAtom q n p≤1 := by
  have hp : 0<(p:ℝ) := by exact_mod_cast p.2.pos
  have hpos : 0 < markedMemoryLineBirthAtom q n p := by
    simpa only [markedMemoryLineBirthAtom,markedMemoryPrimeAtom,one_mul] using
      markedMemoryPrimeAtom_pos (by norm_num : (0:ℝ)<1) hq0 hq1 hlarge
  have hmul : markedMemoryLineBirthAtom q n p*(p:ℝ)≤2 := by
    simpa only [markedMemoryLineBirthAtom,markedMemoryPrimeAtom,one_mul,div_one] using
      markedMemoryPrimeAtom_mul_prime_le (by norm_num : (0:ℝ)<1) hq0 hq1 hlarge
  have hle : markedMemoryLineBirthAtom q n p≤2/(p:ℝ) := (le_div_iff₀ hp).mpr hmul
  have hp2 : (2:ℝ)≤(p:ℝ) := by exact_mod_cast p.2.two_le
  exact ⟨hpos,hle,hle.trans ((div_le_one hp).mpr hp2)⟩

theorem markedMemoryActualPrimeBand_reciprocal_sum {J : Type*}
    (e : J → ℝ) (x : ℝ) (j : J) :
    (∑ p : markedRawActualPrimeBand e x j,(1:ℝ)/(p.1:ℝ))=
      bandReciprocalMass (markedLogPowerBand (e j) x) := by
  let eqv := markedRawPrimeBandEquiv (markedLogPowerBand (e j) x)
    (fun _ hp => (mem_markedLogPowerBand.mp hp).1)
  calc
    _ = ∑ p : markedLogPowerBand (e j) x,(1:ℝ)/(p.1:ℝ) :=
      Equiv.sum_comp eqv (fun p : markedLogPowerBand (e j) x => (1:ℝ)/(p.1:ℝ))
    _ = _ := Finset.sum_coe_sort _ (fun p : ℕ => (1:ℝ)/(p:ℝ))

theorem markedMemoryActualLineBirthAtom_bounds {J : Type*} [Fintype J]
    (e : J → ℝ) (he : ∀ j,(1/10:ℝ)≤e j) :
    ∀ᶠ x : ℝ in atTop, ∀ q : ℝ,0≤q → q≤1 →
      (∀ j (p : markedRawActualPrimeBand e x j),
        0 < markedMemoryLineBirthAtom q (markedMemoryMomentLength x) p.1 ∧
          markedMemoryLineBirthAtom q (markedMemoryMomentLength x) p.1≤1) ∧
      ∀ j,(∑ p : markedRawActualPrimeBand e x j,
        markedMemoryLineBirthAtom q (markedMemoryMomentLength x) p.1)≤2 := by
  have hmass := eventually_all.mpr (fun j => marked_log_power_band_mass_eventually
    (show 0<e j by linarith [he j]))
  filter_upwards [hmass,markedMemoryMomentLength_prime_small_eventually,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with x hm hn hlog
  intro q hq0 hq1
  have hlarge (j : J) (p : markedRawActualPrimeBand e x j) :
      2*(markedMemoryMomentLength x+1)≤(p.1:ℕ)+1 := by
    have hmem : (p.1:ℕ)∈markedLogPowerBand (e j) x :=
      (mem_markedRawPrimeBand _ p.1).mp p.2
    exact hn _ (marked_band_common_lower (he j) hlog hmem)
  constructor
  · intro j p
    have hb := markedMemoryLineBirthAtom_bounds hq0 hq1 p.1 (hlarge j p)
    exact ⟨hb.1,hb.2.2⟩
  · intro j
    calc
      _ ≤ ∑ p : markedRawActualPrimeBand e x j,2/(p.1:ℝ) :=
        Finset.sum_le_sum (fun p _ => (markedMemoryLineBirthAtom_bounds hq0 hq1 p.1 (hlarge j p)).2.1)
      _ = 2*(∑ p : markedRawActualPrimeBand e x j,(1:ℝ)/(p.1:ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p _
        ring
      _ = 2*bandReciprocalMass (markedLogPowerBand (e j) x) := by
        rw [markedMemoryActualPrimeBand_reciprocal_sum]
      _ ≤ 2 := by
        change 2*(∑ p∈markedLogPowerBand (e j) x,(1:ℝ)/(p:ℝ))≤2
        linarith [(hm j).2]

end
end ArtinMatthews
