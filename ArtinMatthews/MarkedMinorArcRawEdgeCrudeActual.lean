module

public import ArtinMatthews.MarkedMinorArcRawEdgeCrudeWeighted
public import ArtinMatthews.MarkedMinorArcDirtyMajorActualTransfer
public import ArtinMatthews.MarkedMinorArcRawGhostActualRow
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

/-! The full signed crude row for the actual tilted log-prime atoms. The
constant is independent of the band exponents and the source slot count. -/
noncomputable section
namespace ArtinMatthews
open Filter
open scoped BigOperators

def markedRawEdgeCrudeActualConstant (K : ℕ) (v₀ H W A L : ℝ) : ℝ :=
  (L*v₀^K)*(16/Real.log 2)^K*H^2*(33*W*(8*A+5))

/-- Actual ν and V are retained, together with both physical endpoints,
the full cross-edge ban and literal old and surviving hit damping. -/
theorem markedRawEdgeCrude_actual_weighted_row_eventually {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j) :
    ∀ᶠ x : ℝ in atTop, ∀ (pads B : ℕ) (Z : Finset (ℤ × ℤ))
      (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
      (r d₀ Y Q q ρ H W A v₀ L : ℝ)
      (χ : MarkedRawState (markedRawActualPrimeBand e x) (pads+1) B Z → ℂ)
      (s : MarkedRawState (markedRawActualPrimeBand e x) (pads+1) B Z) (w : ℤ × ℤ)
      (modifier : MarkedRawEdgeChoice hZ s → ℂ),
      1 ≤ Y → 1 ≤ Q → 0 ≤ q → q ≤ 1 → 0 ≤ ρ → ρ ≤ 1 →
      0 ≤ H → 0 ≤ W → 0 ≤ A → 1 ≤ v₀ → 0 ≤ L →
      (∀ t,‖η t‖ ≤ H) → (∀ t,‖ψ t‖ ≤ W) → (∀ t,ψ t ≠ 0 → |t| ≤ A) →
      (∀ s,‖χ s‖ ≤ 1) → (∀ choice,‖modifier choice‖ ≤ L) →
      markedMinorIntegerDet s.1.1 w=1 → markedMinorIntegerTau r s.1.1 ≠ 0 →
      (∀ v ∈ Z,|markedMinorIntegerTau r v/markedMinorIntegerTau r s.1.1| ≤ 16) →
      markedRawEdgeCrudeWeightedAbsRow (markedRawActualPrimeAtom e q x)
        (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) hZ ψ η d₀ Y Q ρ v₀ χ s modifier ≤
        markedRawEdgeCrudeActualConstant (Fintype.card J) v₀ H W A L*(B+1:ℝ)^(Fintype.card J)*Q^3 := by
  filter_upwards [markedDirty_actual_band_transfer_eventually e he,
    markedRawGhost_actual_band_mass_eventually e he] with x htransfer hmass
  intro pads B Z hZ ψ η r d₀ Y Q q ρ H W A v₀ L χ s w modifier hY hQ hq₀ hq₁ hρ₀ hρ₁
    hH hW hA hv₀ hL hη hψ hsupp hχ hmodifier hw hτ hbox
  have ht := htransfer q hq₀ hq₁
  have hr := markedRawEdgeCrude_weighted_row_le_polynomial (markedRawActualPrimeAtom e q x)
    (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) ht.1 (fun j => (ht.2.1 j).1)
    markedDirty_transfer_constant_one_le (fun j => (ht.2.1 j).2) (by norm_num : (1:ℝ) ≤ 2)
    (hmass q hq₀ hq₁) hZ ψ η r d₀ Y Q ρ H W A v₀ hY hQ hA hρ₀ hρ₁ hH hW hv₀
    hη hψ hsupp χ hχ s w hw hτ hbox modifier hL hmodifier
  apply hr.trans_eq
  rw [show 4*(2/Real.log 2)*2=(16/Real.log 2:ℝ) by ring]
  unfold markedRawEdgeCrudeActualConstant
  ring

end ArtinMatthews
