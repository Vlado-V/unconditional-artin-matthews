module

public import ArtinMatthews.MarkedMinorArcRawEdgeBranches
public import ArtinMatthews.MarkedMinorArcRawBanEnergy
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

/-! The clean part of the literal full store/promote operation inherits the
proved physical clean saving by an exact finite choice identity. -/
namespace ArtinMatthews
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Literal clean part of the actual full store/promote row operation. -/
noncomputable def markedRawEdgeCleanApply {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (f : MarkedRawState P (pads+1) B Z → ℂ) (s : MarkedRawState P (pads+1) B Z) : ℂ :=
  ∑ choice : {choice : MarkedRawEdgeChoice hZ s // MarkedRawEdgeChoiceClean choice},
    markedRawEdgeSummand ν V hZ ψ η d₀ Y Q ρ χ f s choice.1

/-- Actual S*T_clean*S from the full store/promote operation, with the
literal first-good projection and full cross-edge ban. -/
noncomputable def markedRawEdgeFirstGoodCleanSymmetrized {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (r d₀ Y Q ρ : ℝ) (w : Z → ℤ × ℤ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (f : MarkedRawState P (pads+1) B Z → ℂ) :=
  markedRawSlotAverage (markedRawEdgeCleanApply ν V hZ ψ η d₀ Y Q ρ
    (markedRawFirstGoodCutoff r d₀ Y w χ) (markedRawSlotAverage f))

/-- No state, weight, choice multiplicity or damping is changed in passing
from the literal clean branch to the previously estimated operator. -/
theorem markedRawEdgeFirstGoodCleanSymmetrized_eq {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (r d₀ Y Q ρ : ℝ) (w : Z → ℤ × ℤ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (f : MarkedRawState P (pads+1) B Z → ℂ) :
    markedRawEdgeFirstGoodCleanSymmetrized ν V hZ ψ η r d₀ Y Q ρ w χ f=
      markedRawBannedFirstGoodCleanSymmetrized ν hZ ψ η r d₀ Y Q ρ w χ f := by
  unfold markedRawEdgeFirstGoodCleanSymmetrized markedRawBannedFirstGoodCleanSymmetrized
    markedRawBannedFirstGoodCleanApply
  congr 1
  funext s
  exact markedRawEdge_clean_sum ν V hZ ψ η d₀ Y Q ρ _ _ s

set_option backward.isDefEq.respectTransparency false in
/-- Unconditional logarithmic clean saving for the literal store/promote
model itself. All actual ν/factorial masses, indexed particles and source
edge choice multiplicities are retained, with A0=G+6 independent of bands. -/
theorem marked_minor_actual_edge_clean_symmetrized_energy {J : Type*} [Fintype J] [DecidableEq J]
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
        ‖markedRawEdgeFirstGoodCleanSymmetrized (markedRawActualPrimeAtom e q x)
          (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) hZ ψ η r d₀ Y
          ((Real.log x)^(G+6)) ρ w χ f s‖^2) ≤
      ((Real.log x)^(-G))^2*∑ s, markedRawStateMass (markedRawActualPrimeAtom e q x) s*‖f s‖^2 := by
  filter_upwards [marked_minor_actual_raw_banned_clean_symmetrized_energy e he hinj ψ η hη hηnorm
    hG hH hc hL hK hψ] with x hx
  intro B Z hZ q r d₀ Y ρ w χ hq₀ hq₁ hd₀ hρ₀ hρ₁ hYlo hYhi hw hτ hratio hχ f
  rw [markedRawEdgeFirstGoodCleanSymmetrized_eq (pads := ⌊(Real.log x)^(1/100:ℝ)⌋₊)
    (markedRawActualPrimeAtom e q x) (fun j => bandReciprocalMass (markedLogPowerBand (e j) x))
    hZ ψ η r d₀ Y ((Real.log x)^(G+6)) ρ w χ f]
  exact hx B Z hZ q r d₀ Y ρ w χ hq₀ hq₁ hd₀ hρ₀ hρ₁ hYlo hYhi hw hτ hratio hχ f

end ArtinMatthews
