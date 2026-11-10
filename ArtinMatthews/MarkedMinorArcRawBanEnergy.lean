module

public import ArtinMatthews.MarkedMinorArcBanRawEntry
public import ArtinMatthews.MarkedMinorArcRawShiftGeometry
public import ArtinMatthews.MarkedMinorArcRawSlotAverage
public import ArtinMatthews.MarkedMinorArcBanRawSchur
public import ArtinMatthews.MarkedMinorArcRawBanRestored
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

/-! Actual full-state clean energy with the source cross-edge ban restored,
including both independent uniform source slot symmetrizations. -/
namespace ArtinMatthews
open Filter
open scoped BigOperators

/-- Literal physical first-good clean action with the full cross-edge ban. -/
noncomputable def markedRawBannedFirstGoodCleanApply {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (r d₀ Y Q ρ : ℝ) (w : Z → ℤ × ℤ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (f : MarkedRawState P (pads+1) B Z → ℂ) :=
  markedRawCleanApply ν (markedRawBannedCleanKernel
    (markedRawCleanKernel hZ ψ η d₀ Y Q ρ (markedRawFirstGoodCutoff r d₀ Y w χ))) f

/-- The literal source S*T_clean*S with all original physical edge bans. -/
noncomputable def markedRawBannedFirstGoodCleanSymmetrized {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (r d₀ Y Q ρ : ℝ) (w : Z → ℤ × ℤ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (f : MarkedRawState P (pads+1) B Z → ℂ) :=
  markedRawSlotAverage (markedRawBannedFirstGoodCleanApply ν hZ ψ η r d₀ Y Q ρ w χ (markedRawSlotAverage f))

/-- Genuine clean S*T*S saving on the complete actual truncated raw state,
with its growing active-slot count, actual factorial memory measure, true
first-good test and literal cross-edge ban. No norm estimate is a premise. -/
theorem marked_minor_actual_raw_banned_clean_symmetrized_energy {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j, (1/10:ℝ) ≤ e j) (hinj : Function.Injective e)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (hη : Function.support η ⊆ Set.Icc 1 4) (hηnorm : ∀ t, ‖η t‖ ≤ 1)
    {G H c L K : ℝ} (hG : 0 < G) (hH : 1 ≤ H) (hc : 0 < c) (hL : 0 ≤ L) (hK : 0 ≤ K)
    (hψ : Function.support ψ ⊆ Set.Icc (-K) K) :
    ∀ᶠ x : ℝ in atTop, ∀ (B : ℕ) (Z : Finset (ℤ × ℤ))
      (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (q r d₀ Y ρ : ℝ)
      (w : Z → ℤ × ℤ) (χ : MarkedRawState (markedRawActualPrimeBand e x) (markedPadSlots x) B Z → ℂ),
      0 ≤ q → q ≤ 1 → 0 < d₀ → 0 ≤ ρ → ρ ≤ 1 →
      Real.exp ((Real.log x)^(1/10:ℝ)) ≤ Y → Y ≤ Real.exp (H*(Real.log x)^(1/5:ℝ)) →
      (∀ z, markedMinorIntegerDet z.1 (w z)=1) →
      (∀ z ∈ Z, c ≤ |markedMinorIntegerTau r z| ∧ |markedMinorIntegerTau r z| ≤ L) →
      (∀ z v : Z, |markedMinorIntegerTau r v.1/markedMinorIntegerTau r z.1| ≤ 16) →
      (∀ s, ‖χ s‖ ≤ 1) → ∀ f : MarkedRawState (markedRawActualPrimeBand e x) (markedPadSlots x) B Z → ℂ,
      (∑ s, markedRawStateMass (markedRawActualPrimeAtom e q x) s*
        ‖markedRawBannedFirstGoodCleanSymmetrized (markedRawActualPrimeAtom e q x) hZ ψ η r d₀ Y
          ((Real.log x)^(G+6)) ρ w χ f s‖^2) ≤
      ((Real.log x)^(-G))^2*∑ s, markedRawStateMass (markedRawActualPrimeAtom e q x) s*‖f s‖^2 := by
  classical
  filter_upwards [marked_minor_actual_raw_banned_clean_opNorm e he hinj ψ η hη hηnorm hG hH hc hL hK hψ,
    marked_actual_tilted_atom_comparison_eventually e he,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with x hx hν hlog
  intro B Z hZ q r d₀ Y ρ w χ hq₀ hq₁ hd₀ hρ₀ hρ₁ hYlo hYhi hw hτ hratio hχ f
  have hνpos : ∀ j p, 0 ≤ markedRawActualPrimeAtom e q x j p := by
    intro j p
    rw [markedRawActualPrimeAtom_eq_tilted]
    exact (hν q hq₀ hq₁ j _).1
  have hclean := markedRawCleanApply_energy_of_fiber_norm (markedRawActualPrimeAtom e q x) hνpos
    (markedRawBannedCleanKernel (markedRawCleanKernel hZ ψ η d₀ Y ((Real.log x)^(G+6)) ρ
      (markedRawFirstGoodCutoff r d₀ Y w χ)))
    (Real.rpow_nonneg (by linarith : (0:ℝ)≤Real.log x) _)
    (fun bg => hx B Z hZ q r d₀ Y ρ w χ bg hq₀ hq₁ hd₀ hρ₀ hρ₁ hYlo hYhi hw hτ hratio hχ)
    (markedRawSlotAverage f)
  exact (markedRawSlotAverage_energy_le _ hνpos _).trans
    (hclean.trans (mul_le_mul_of_nonneg_left
      (markedRawSlotAverage_energy_le _ hνpos f) (sq_nonneg _)))

end ArtinMatthews
