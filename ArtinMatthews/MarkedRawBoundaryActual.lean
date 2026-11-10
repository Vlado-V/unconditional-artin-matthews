module

public import ArtinMatthews.MarkedRawBoundary
public import ArtinMatthews.MarkedMemoryTiltActual
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

/-! The actual PD04 tilted boundary has bounded norm despite the growing
full-list length. The proof uses the sharp relative atom error and retains
the true memory factorial and every ordered active tuple. -/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace ArtinMatthews

theorem markedRawBoundary_actual_energy_le_envelope {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j, (1/10:ℝ) ≤ e j) :
    ∀ᶠ x : ℝ in atTop, ∀ (q : ℝ), 0 ≤ q → q ≤ 1 →
      ∀ (B : ℕ) (Z : Finset (ℤ × ℤ)) (z₀ : Z),
      markedRawBoundaryEnergy (markedRawActualPrimeAtom e q x) (markedPadSlots x) B z₀ ≤
        Real.exp (markedMemoryBoundaryEnvelope (Fintype.card J) x) := by
  filter_upwards [markedMemory_actual_tilt_mass_error e he,
    marked_actual_tilted_atom_comparison_eventually e he,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))] with x hmass hν hlog
  intro q hq₀ hq₁ B Z z₀
  have hnonneg : ∀ j p, 0 ≤ markedRawActualPrimeAtom e q x j p := by
    intro j p
    rw [markedRawActualPrimeAtom_eq_tilted]
    exact (hν q hq₀ hq₁ j _).1
  have hs : ∀ j, (∑ p : ↥(markedRawActualPrimeBand e x j), markedRawActualPrimeAtom e q x j p) ≤
      1+markedMemoryTiltError x := by
    intro j
    have hh := (abs_le.mp (hmass q hq₀ hq₁ j)).2
    linarith
  exact (markedRawBoundaryEnergy_le_exp _ hnonneg _ B z₀ hs).trans
    (Real.exp_le_exp.mpr (markedMemory_boundary_exponent_le (Fintype.card J) hlog))

/-- Exact source boundary bound, uniformly in q, the actual root position,
and every total-memory cutoff. In particular it applies to B=ceil(L²).
The fixed bound two is obtained after the true growing M has been included,
not by raising a fixed per-band bound to M. -/
theorem markedRawBoundary_actual_energy_le_two {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j, (1/10:ℝ) ≤ e j) :
    ∀ᶠ x : ℝ in atTop, ∀ (q : ℝ), 0 ≤ q → q ≤ 1 →
      ∀ (B : ℕ) (Z : Finset (ℤ × ℤ)) (z₀ : Z),
      markedRawBoundaryEnergy (markedRawActualPrimeAtom e q x) (markedPadSlots x) B z₀ ≤ 2 := by
  filter_upwards [markedRawBoundary_actual_energy_le_envelope e he,
    (markedMemoryBoundaryEnvelope_tendsto (Fintype.card J)).eventually
      (Iio_mem_nhds (by positivity : 0 < Real.log 2))] with x hx henv
  intro q hq₀ hq₁ B Z z₀
  apply (hx q hq₀ hq₁ B Z z₀).trans
  calc
    Real.exp (markedMemoryBoundaryEnvelope (Fintype.card J) x) ≤ Real.exp (Real.log 2) :=
      Real.exp_le_exp.mpr henv.le
    _ = 2 := Real.exp_log (by norm_num)

/-- An arbitrarily small upper norm error is also uniform over q, roots,
and truncations. This is stronger than the fixed bound needed in moments. -/
theorem markedRawBoundary_actual_energy_le_one_add {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j, (1/10:ℝ) ≤ e j) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ (q : ℝ), 0 ≤ q → q ≤ 1 →
      ∀ (B : ℕ) (Z : Finset (ℤ × ℤ)) (z₀ : Z),
      markedRawBoundaryEnergy (markedRawActualPrimeAtom e q x) (markedPadSlots x) B z₀ ≤ 1+ε := by
  filter_upwards [markedRawBoundary_actual_energy_le_envelope e he,
    (markedMemoryBoundaryEnvelope_tendsto (Fintype.card J)).eventually
      (Iio_mem_nhds (Real.log_pos (by linarith : 1 < 1+ε)))] with x hx henv
  intro q hq₀ hq₁ B Z z₀
  apply (hx q hq₀ hq₁ B Z z₀).trans
  calc
    Real.exp (markedMemoryBoundaryEnvelope (Fintype.card J) x) ≤ Real.exp (Real.log (1+ε)) :=
      Real.exp_le_exp.mpr henv.le
    _ = 1+ε := Real.exp_log (by linarith)

end ArtinMatthews
