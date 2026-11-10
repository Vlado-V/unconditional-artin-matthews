module

public import ArtinMatthews.MarkedMinorArcRawGhostActualRow
public import ArtinMatthews.MarkedMinorArcRawMemoryAmbient
public import ArtinMatthews.MarkedMinorArcRawGhostEnergyBound
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! The square-root weighted L² bound for the literal physical ghost action. -/
namespace ArtinMatthews
noncomputable section
open Filter
open scoped BigOperators

/-- The actual ghost has a uniform weighted L² constant with no cutoff or
state-count loss. This is the square root of the proved physical energy inequality. -/
theorem marked_minor_actual_raw_ghost_sqrt_energy
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j, (1/10:ℝ) ≤ e j) {q ρ : ℝ}
    (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) (hρ : 0 < ρ) (hgap : Real.sqrt q < ρ^2) :
    ∀ᶠ x : ℝ in atTop, ∀ (qStage : ℝ), 0 ≤ qStage → qStage ≤ Real.sqrt q →
      ∀ (M B : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
        (f : MarkedRawState (markedRawActualPrimeBand e x) M B Z → ℂ),
      (∀ z a, MarkedRawMemorySymmetric (fun m => f (z, (a, m)))) →
      Real.sqrt (∑ s, markedRawStateMass (markedRawActualPrimeAtom e q x) s *
        ‖markedRawGhostApply (markedRawActualPrimeAtom e q x)
          (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) qStage ρ hZ f s‖^2) ≤
      Real.exp ((Fintype.card J : ℝ) * (2 * markedRawGhostSchurParameter q ρ / ρ)) *
        Real.sqrt (∑ s, markedRawStateMass (markedRawActualPrimeAtom e q x) s * ‖f s‖^2) := by
  filter_upwards [marked_minor_actual_raw_ghost_energy e he hq₀ hq₁ hρ hgap] with x hx
  intro qStage hqs₀ hqs M B Z hZ f hf
  have hh := Real.sqrt_le_sqrt (hx qStage hqs₀ hqs M B Z hZ f hf)
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Real.exp_pos _).le] at hh
  exact hh

end
end ArtinMatthews
