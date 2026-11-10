module

public import ArtinMatthews.MarkedMinorArcRawEdgeCrudeActual
public import ArtinMatthews.MarkedMinorArcRawGhostActualRow
public import ArtinMatthews.MarkedMinorArcRawMemoryAmbient
public import ArtinMatthews.MarkedMemoryGoodBoundary
public import ArtinMatthews.MarkedMinorArcRawEdgeCrudeEnergy
public import ArtinMatthews.MarkedMinorArcRawGhostEnergyBound
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

/-! Cauchy at an actual bad-state insertion. The proved crude edge and
ghost energies control the other side; the bad energy is kept explicit. -/
namespace ArtinMatthews
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def markedRawBadPairing {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ)
    {M B : ℕ} {Z : Finset (ℤ × ℤ)} (G : MarkedRawState P M B Z → Prop)
    (u v : MarkedRawState P M B Z → ℂ) : ℂ :=
  ∑ s,(markedRawStateMass ν s:ℂ)*star (if G s then 0 else u s)*v s

theorem markedRawBadPairing_cauchy {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (hν : ∀ j p,0 ≤ ν j p)
    {M B : ℕ} {Z : Finset (ℤ × ℤ)} (G : MarkedRawState P M B Z → Prop)
    (u v : MarkedRawState P M B Z → ℂ) :
    ‖markedRawBadPairing ν G u v‖^2 ≤
      (∑ s,markedRawStateMass ν s*‖if G s then 0 else u s‖^2)*
        ∑ s,markedRawStateMass ν s*‖v s‖^2 :=
  markedWeightedBoundary_cauchy (markedRawStateMass ν) (markedRawStateMass_nonneg ν hν)
    (fun s => if G s then 0 else u s) v

theorem markedRawBadPairing_edge_actual
    {J : Type*} [Fintype J] [DecidableEq J] (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j)
    (hinj : Function.Injective e) :
    ∀ᶠ x : ℝ in atTop,∀ (pads B : ℕ) (Z : Finset (ℤ × ℤ))
      (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
      (r d₀ Y Q q ρ H W A v₀ : ℝ) (w : Z → ℤ × ℤ)
      (χ u v : MarkedRawState (markedRawActualPrimeBand e x) (pads+1) B Z → ℂ)
      (G : MarkedRawState (markedRawActualPrimeBand e x) (pads+1) B Z → Prop),
      1 ≤ Y → 1 ≤ Q → 0 ≤ q → q ≤ 1 → 0 ≤ ρ → ρ ≤ 1 →
      0 ≤ H → 0 ≤ W → 0 ≤ A → 1 ≤ v₀ →
      (∀ t,‖η t‖ ≤ H) → (∀ t,‖ψ t‖ ≤ W) → (∀ t,ψ t ≠ 0 → |t| ≤ A) →
      (∀ s,‖χ s‖ ≤ 1) → (∀ z a,MarkedRawMemorySymmetric (fun m => χ (z,(a,m)))) →
      (∀ z a,MarkedRawMemorySymmetric (fun m => v (z,(a,m)))) →
      (∀ z,markedMinorIntegerDet z.1 (w z)=1) → (∀ z : Z,markedMinorIntegerTau r z.1 ≠ 0) →
      (∀ z t : Z,|markedMinorIntegerTau r t.1/markedMinorIntegerTau r z.1| ≤ 16) →
      ‖markedRawBadPairing (markedRawActualPrimeAtom e q x) G u
        (markedRawEdgeApply (markedRawActualPrimeAtom e q x)
          (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) hZ ψ η d₀ Y Q ρ χ v)‖^2 ≤
        (markedRawEdgeCrudeActualConstant (Fintype.card J) v₀ H W A 1*(B+1:ℝ)^(Fintype.card J)*Q^3)^2 *
          (∑ s,markedRawStateMass (markedRawActualPrimeAtom e q x) s*‖if G s then 0 else u s‖^2) *
          (∑ s,markedRawStateMass (markedRawActualPrimeAtom e q x) s*‖v s‖^2) := by
  filter_upwards [markedRawEdgeApply_actual_crude_energy_eventually e he hinj,
    markedRawActualStateMass_nonneg_eventually e he] with x hx hm
  intro pads B Z hZ ψ η r d₀ Y Q q ρ H W A v₀ w χ u v G hY hQ hq₀ hq₁ hρ₀ hρ₁
    hH hW hA hv₀ hη hψ hsupp hχ hχsym hv hw hτ hbox
  have hb := markedWeightedBoundary_cauchy (markedRawStateMass (markedRawActualPrimeAtom e q x))
    (hm q hq₀ hq₁ _ B Z) (fun s => if G s then 0 else u s)
    (markedRawEdgeApply (markedRawActualPrimeAtom e q x)
      (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) hZ ψ η d₀ Y Q ρ χ v)
  have he := hx pads B Z hZ ψ η r d₀ Y Q q ρ H W A v₀ w χ v hY hQ hq₀ hq₁ hρ₀ hρ₁
    hH hW hA hv₀ hη hψ hsupp hχ hχsym hv hw hτ hbox
  apply hb.trans
  exact (mul_le_mul_of_nonneg_left he (Finset.sum_nonneg
    (fun s _ => mul_nonneg (hm q hq₀ hq₁ _ B Z s) (sq_nonneg _)))).trans_eq (by ring)

theorem markedRawBadPairing_ghost_actual
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j) {q ρ : ℝ}
    (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) (hρ : 0 < ρ) (hgap : Real.sqrt q < ρ^2) :
    ∀ᶠ x : ℝ in atTop,∀ qStage : ℝ,0 ≤ qStage → qStage ≤ Real.sqrt q →
      ∀ (M B : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
        (u v : MarkedRawState (markedRawActualPrimeBand e x) M B Z → ℂ)
        (G : MarkedRawState (markedRawActualPrimeBand e x) M B Z → Prop),
      (∀ z a,MarkedRawMemorySymmetric (fun m => v (z,(a,m)))) →
      ‖markedRawBadPairing (markedRawActualPrimeAtom e q x) G u
        (markedRawGhostApply (markedRawActualPrimeAtom e q x)
          (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) qStage ρ hZ v)‖^2 ≤
        (Real.exp ((Fintype.card J:ℝ)*(2*markedRawGhostSchurParameter q ρ/ρ)))^2 *
          (∑ s,markedRawStateMass (markedRawActualPrimeAtom e q x) s*‖if G s then 0 else u s‖^2) *
          (∑ s,markedRawStateMass (markedRawActualPrimeAtom e q x) s*‖v s‖^2) := by
  filter_upwards [marked_minor_actual_raw_ghost_energy e he hq₀ hq₁ hρ hgap,
    markedRawActualStateMass_nonneg_eventually e he] with x hx hm
  intro qStage hqs₀ hqs M B Z hZ u v G hv
  have hb := markedWeightedBoundary_cauchy (markedRawStateMass (markedRawActualPrimeAtom e q x))
    (hm q hq₀ hq₁ M B Z) (fun s => if G s then 0 else u s)
    (markedRawGhostApply (markedRawActualPrimeAtom e q x)
      (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) qStage ρ hZ v)
  have he := hx qStage hqs₀ hqs M B Z hZ v hv
  apply hb.trans
  exact (mul_le_mul_of_nonneg_left he (Finset.sum_nonneg
    (fun s _ => mul_nonneg (hm q hq₀ hq₁ M B Z s) (sq_nonneg _)))).trans_eq (by ring)

end
end ArtinMatthews
