module

public import ArtinMatthews.MarkedMemoryConditionalGhostRow
public import ArtinMatthews.MarkedMemoryConditionalEdgeRow
public import ArtinMatthews.MarkedMemoryBirthAtom
public import ArtinMatthews.MarkedMemoryEdgePivotMass
public import ArtinMatthews.MarkedMemoryGhostPivotMass
public import ArtinMatthews.MarkedMinorArcRawEdgeCrudeActual
public import ArtinMatthews.MarkedMinorArcRawGhostActualRow
public import ArtinMatthews.MarkedMemoryEdgePivotActual
public import ArtinMatthews.MarkedMemoryGhostPivotActual
public import ArtinMatthews.MarkedMinorArcDirtyMajorActualTransfer
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

/-! Conditional row bounds on the original chronological choice types.
Both slot averages are literal; every pivot atom cost is discharged from
the actual tilted law, with no conditional probability premise. -/

noncomputable section
namespace ArtinMatthews
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem markedMemoryGhostPivot_choice_row_eventually
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j, (1/10:ℝ) ≤ e j) {q ρ : ℝ}
    (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) (hρ : 0 < ρ) (hgap : Real.sqrt q < ρ^2) :
    ∀ᶠ x : ℝ in atTop, ∀ (M B N slots : ℕ)
      (σ : Equiv.Perm (MarkedMemoryPotentialAddress J M B N)) (t : Fin (N+1))
      (old : MarkedMemoryPotentialAddress J M B N → Option Nat.Primes)
      (qStage : ℝ), 0 ≤ qStage → qStage ≤ Real.sqrt q →
      ∀ (Z : Finset (ℤ × ℤ)) (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
        (s : MarkedRawState (markedRawActualPrimeBand e x) slots B Z),
      markedMemoryConditionalGhostRow (markedRawActualPrimeAtom e q x)
        (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) qStage ρ
        (markedRawGhostSchurParameter q ρ) hZ s
        (fun _ l births => markedMemoryGhostPivotGate σ t old l.1 births) ≤
      (markedMemoryBirthAtomEnvelope x)^(markedMemoryStageNonpivots σ (2*t.1+1)).card*
        Real.exp ((Fintype.card J:ℝ)*(2*markedRawGhostSchurParameter q ρ/ρ)) := by
  filter_upwards [markedMemoryGhostPivot_actual_weighted_row_eventually e he hq₀ hq₁ hρ hgap] with x hx
  intro M B N slots σ t old qStage hqs₀ hqs Z hZ s
  rw [markedMemoryConditionalGhostRow_eq]
  exact hx M B N σ t old qStage hqs₀ hqs s.2.2 s.1.1 (hZ _ s.1.2)

theorem markedMemoryEdgePivot_choice_row_eventually
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j, (1/10:ℝ) ≤ e j) :
    ∀ᶠ x : ℝ in atTop, ∀ (M B N : ℕ)
      (σ : Equiv.Perm (MarkedMemoryPotentialAddress J M B N)) (t : Fin N)
      (old : MarkedMemoryPotentialAddress J M B N → Option Nat.Primes)
      (pads : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
      (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (r d₀ Y Q q ρ H W A v₀ : ℝ)
      (χ : MarkedRawState (markedRawActualPrimeBand e x) (pads+1) B Z → ℂ)
      (s : MarkedRawState (markedRawActualPrimeBand e x) (pads+1) B Z) (w : ℤ × ℤ),
      1 ≤ Y → 1 ≤ Q → 0 ≤ q → q ≤ 1 → 0 ≤ ρ → ρ ≤ 1 →
      0 ≤ H → 0 ≤ W → 0 ≤ A → 1 ≤ v₀ →
      (∀ u,‖η u‖ ≤ H) → (∀ u,‖ψ u‖ ≤ W) → (∀ u,ψ u≠0 → |u| ≤ A) →
      (∀ s,‖χ s‖ ≤ 1) → markedMinorIntegerDet s.1.1 w=1 →
      markedMinorIntegerTau r s.1.1≠0 →
      (∀ v∈Z,|markedMinorIntegerTau r v/markedMinorIntegerTau r s.1.1| ≤ 16) →
      markedMemoryConditionalEdgeRow (markedRawActualPrimeAtom e q x)
        (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) hZ ψ η d₀ Y Q ρ v₀ χ
        (fun s => markedMemoryEdgePivotGate σ t old hZ s) s ≤
      (markedMemoryBirthAtomEnvelope x)^(markedMemoryStageNonpivots σ (2*t.1+2)).card*
        (markedRawEdgeCrudeActualConstant (Fintype.card J) v₀ H W A 1*(B+1:ℝ)^(Fintype.card J)*Q^3) := by
  filter_upwards [markedMemoryEdgePivot_actual_weighted_row_eventually e he,
    markedDirty_actual_band_transfer_eventually e he] with x hx htransfer
  intro M B N σ t old pads Z hZ ψ η r d₀ Y Q q ρ H W A v₀ χ s w
    hY hQ hq₀ hq₁ hρ₀ hρ₁ hH hW hA hv₀ hη hψ hsupp hχ hw hτ hbox
  have ht := htransfer q hq₀ hq₁
  apply markedMemoryConditionalEdgeRow_le (markedRawActualPrimeAtom e q x)
    (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) ht.1 (fun j => (ht.2.1 j).1)
    hZ ψ η d₀ Y Q ρ v₀ χ (fun s => markedMemoryEdgePivotGate σ t old hZ s) s
  intro τ
  exact hx M B N σ t old pads Z hZ ψ η r d₀ Y Q q ρ H W A v₀ χ
    (markedRawSlotEquiv τ s) w hY hQ hq₀ hq₁ hρ₀ hρ₁ hH hW hA hv₀ hη hψ hsupp hχ hw hτ hbox

end ArtinMatthews
