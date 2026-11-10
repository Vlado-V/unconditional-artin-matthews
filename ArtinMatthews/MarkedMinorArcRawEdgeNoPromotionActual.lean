module

public import ArtinMatthews.MarkedMinorArcRawEdgeNoPromotion
public import ArtinMatthews.MarkedMinorArcDirtyRawEdgeOmissionAverage
public import ArtinMatthews.MarkedMinorArcDirtyMajorActualTransfer
public import ArtinMatthews.MarkedMinorArcDirtyMajorChoiceWeighted
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

/-! The no-promotion weighted row is polynomial in Q and independent of
the pending cutoff B. This is the crude side of the one-sided sectors. -/
namespace ArtinMatthews
noncomputable section
open Filter
open scoped BigOperators

theorem markedRawEdgeNoPromotionWeightedRow_polynomial
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) (hν : ∀ j p,0 ≤ ν j p) (hV : ∀ j,0 < V j)
    {N : ℝ} (hN : 1 ≤ N) (hνN : ∀ j,(∑ p,ν j p) ≤ N)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (r d₀ Y Q ρ H W A v₀ : ℝ)
    (hY : 1 ≤ Y) (hQ : 1 ≤ Q) (hA : 0 ≤ A) (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1)
    (hH : 0 ≤ H) (hW : 0 ≤ W) (hv₀ : 1 ≤ v₀)
    (hη : ∀ t,‖η t‖ ≤ H) (hψ : ∀ t,‖ψ t‖ ≤ W) (hsupp : ∀ t,ψ t ≠ 0 → |t| ≤ A)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (hχ : ∀ s,‖χ s‖ ≤ 1)
    (s : MarkedRawState P (pads+1) B Z) (w : ℤ × ℤ) (hw : markedMinorIntegerDet s.1.1 w=1)
    (hτ : markedMinorIntegerTau r s.1.1 ≠ 0)
    (hbox : ∀ v ∈ Z,|markedMinorIntegerTau r v/markedMinorIntegerTau r s.1.1| ≤ 16)
    (modifier : MarkedRawEdgeChoice hZ s → ℂ) {L : ℝ} (hL : 0 ≤ L) (hmodifier : ∀ c,‖modifier c‖ ≤ L) :
    markedRawEdgeNoPromotionWeightedRow ν V hZ ψ η d₀ Y Q ρ v₀ χ s modifier ≤
      (L*v₀^(Fintype.card J))*(2*N)^(Fintype.card J)*H^2*(33*W*(8*A+5))*Q^3 := by
  have hb := markedRawEdgeCrude_empty_row_le ν V hν hN hνN hZ ψ η r d₀ Y Q ρ H W A
    (zero_lt_one.trans_le hY) (zero_le_one.trans hQ) hA hρ₀ hρ₁ hH hW hη hψ hsupp χ hχ s w hw hτ hbox
  have hm := markedRawEdgeNoPromotionWeightedRow_le ν V hν hV hZ ψ η d₀ Y Q ρ v₀ hv₀ χ s modifier hL hmodifier
  have hv : 0 ≤ v₀ := zero_le_one.trans hv₀
  have hN₀ : 0 ≤ N := zero_le_one.trans hN
  have hp : 0 ≤ L*v₀^(Fintype.card J) := by positivity
  apply (hm.trans (mul_le_mul_of_nonneg_left hb hp)).trans
  have hk := mul_le_mul_of_nonneg_left (markedRawEdgeCrude_kernel_factor_le_polynomial (A := A) hY hQ hW)
    (show 0 ≤ (L*v₀^(Fintype.card J))*(2*N)^(Fintype.card J)*H^2 by positivity)
  convert hk using 1 <;> ring

def markedRawEdgeNoPromotionConstant (K : ℕ) (v₀ H W A L : ℝ) : ℝ :=
  (L*v₀^K)*(4:ℝ)^K*H^2*(33*W*(8*A+5))

theorem markedRawEdgeNoPromotion_actual_weighted_row_eventually
    {J : Type*} [Fintype J] [DecidableEq J] (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j) :
    ∀ᶠ x : ℝ in atTop, ∀ (pads B : ℕ) (Z : Finset (ℤ × ℤ))
      (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
      (r d₀ Y Q q ρ H W A v₀ L : ℝ)
      (χ : MarkedRawState (markedRawActualPrimeBand e x) (pads+1) B Z → ℂ)
      (s : MarkedRawState (markedRawActualPrimeBand e x) (pads+1) B Z) (w : ℤ × ℤ)
      (modifier : MarkedRawEdgeChoice hZ s → ℂ),
      1 ≤ Y → 1 ≤ Q → 0 ≤ q → q ≤ 1 → 0 ≤ ρ → ρ ≤ 1 → 0 ≤ H → 0 ≤ W → 0 ≤ A → 1 ≤ v₀ → 0 ≤ L →
      (∀ t,‖η t‖ ≤ H) → (∀ t,‖ψ t‖ ≤ W) → (∀ t,ψ t ≠ 0 → |t| ≤ A) →
      (∀ s,‖χ s‖ ≤ 1) → (∀ c,‖modifier c‖ ≤ L) → markedMinorIntegerDet s.1.1 w=1 →
      markedMinorIntegerTau r s.1.1 ≠ 0 →
      (∀ v ∈ Z,|markedMinorIntegerTau r v/markedMinorIntegerTau r s.1.1| ≤ 16) →
      markedRawEdgeNoPromotionWeightedRow (markedRawActualPrimeAtom e q x)
        (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) hZ ψ η d₀ Y Q ρ v₀ χ s modifier ≤
        markedRawEdgeNoPromotionConstant (Fintype.card J) v₀ H W A L*Q^3 := by
  filter_upwards [markedDirty_actual_band_transfer_eventually e he,
    markedRawGhost_actual_band_mass_eventually e he] with x htransfer hmass
  intro pads B Z hZ ψ η r d₀ Y Q q ρ H W A v₀ L χ s w modifier
    hY hQ hq₀ hq₁ hρ₀ hρ₁ hH hW hA hv₀ hL hη hψ hsupp hχ hmodifier hw hτ hbox
  have ht := htransfer q hq₀ hq₁
  have hh := markedRawEdgeNoPromotionWeightedRow_polynomial (markedRawActualPrimeAtom e q x)
    (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) ht.1 (fun j => (ht.2.1 j).1)
    (by norm_num : (1:ℝ) ≤ 2) (hmass q hq₀ hq₁) hZ ψ η r d₀ Y Q ρ H W A v₀ hY hQ hA hρ₀ hρ₁
    hH hW hv₀ hη hψ hsupp χ hχ s w hw hτ hbox modifier hL hmodifier
  simpa only [markedRawEdgeNoPromotionConstant,show (2:ℝ)*2=4 by norm_num] using hh

def markedRawEdgeNoPromotionSymWeightedRow {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ v₀ : ℝ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (s : MarkedRawState P (pads+1) B Z)
    (modifier : (σ : J → Equiv.Perm (Fin (pads+1))) → MarkedRawEdgeChoice hZ (markedRawSlotEquiv σ s) → ℂ) : ℝ :=
  ∑ σ : J → Equiv.Perm (Fin (pads+1)),markedDirtySourceSlotWeight pads σ*
    markedRawEdgeNoPromotionWeightedRow ν V hZ ψ η d₀ Y Q ρ v₀ χ (markedRawSlotEquiv σ s) (modifier σ)

theorem markedRawEdgeNoPromotion_actual_sym_row_eventually
    {J : Type*} [Fintype J] [DecidableEq J] (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j) :
    ∀ᶠ x : ℝ in atTop, ∀ (pads B : ℕ) (Z : Finset (ℤ × ℤ))
      (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
      (r d₀ Y Q q ρ H W A v₀ L : ℝ)
      (χ : MarkedRawState (markedRawActualPrimeBand e x) (pads+1) B Z → ℂ)
      (s : MarkedRawState (markedRawActualPrimeBand e x) (pads+1) B Z)
      (w : ℤ × ℤ)
      (modifier : (σ : J → Equiv.Perm (Fin (pads+1))) → MarkedRawEdgeChoice hZ (markedRawSlotEquiv σ s) → ℂ),
      1 ≤ Y → 1 ≤ Q → 0 ≤ q → q ≤ 1 → 0 ≤ ρ → ρ ≤ 1 → 0 ≤ H → 0 ≤ W → 0 ≤ A → 1 ≤ v₀ → 0 ≤ L →
      (∀ t,‖η t‖ ≤ H) → (∀ t,‖ψ t‖ ≤ W) → (∀ t,ψ t ≠ 0 → |t| ≤ A) →
      (∀ s,‖χ s‖ ≤ 1) → (∀ σ c,‖modifier σ c‖ ≤ L) → markedMinorIntegerDet s.1.1 w=1 →
      markedMinorIntegerTau r s.1.1 ≠ 0 →
      (∀ v ∈ Z,|markedMinorIntegerTau r v/markedMinorIntegerTau r s.1.1| ≤ 16) →
      markedRawEdgeNoPromotionSymWeightedRow (markedRawActualPrimeAtom e q x)
        (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) hZ ψ η d₀ Y Q ρ v₀ χ s modifier ≤
        markedRawEdgeNoPromotionConstant (Fintype.card J) v₀ H W A L*Q^3 := by
  filter_upwards [markedRawEdgeNoPromotion_actual_weighted_row_eventually e he] with x hx
  intro pads B Z hZ ψ η r d₀ Y Q q ρ H W A v₀ L χ s w modifier
    hY hQ hq₀ hq₁ hρ₀ hρ₁ hH hW hA hv₀ hL hη hψ hsupp hχ hmodifier hw hτ hbox
  unfold markedRawEdgeNoPromotionSymWeightedRow
  calc
    _ ≤ ∑ σ : J → Equiv.Perm (Fin (pads+1)),markedDirtySourceSlotWeight pads σ*
        (markedRawEdgeNoPromotionConstant (Fintype.card J) v₀ H W A L*Q^3) := by
      apply Finset.sum_le_sum
      intro σ _
      apply mul_le_mul_of_nonneg_left _ (by unfold markedDirtySourceSlotWeight; positivity)
      exact hx pads B Z hZ ψ η r d₀ Y Q q ρ H W A v₀ L χ (markedRawSlotEquiv σ s) w (modifier σ)
        hY hQ hq₀ hq₁ hρ₀ hρ₁ hH hW hA hv₀ hL hη hψ hsupp hχ (hmodifier σ) hw hτ hbox
    _ = _ := by rw [← Finset.sum_mul,markedDirtySourceSlotWeight_total,one_mul]

end
end ArtinMatthews
