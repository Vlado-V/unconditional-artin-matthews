module

public import ArtinMatthews.MarkedMinorArcRawEdgeCrudeActual
public import ArtinMatthews.MarkedMinorArcRawEdgeChargedRow
public import ArtinMatthews.MarkedMinorArcDirtyMajorActualTransfer
public import ArtinMatthews.MarkedMinorArcRawEdgeChargedReverse
public import ArtinMatthews.MarkedMinorArcRawGhostActualRow
public import ArtinMatthews.MarkedMinorArcRawProductMass
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

/-! Actual weighted crude rows for arbitrary charges, including the
literal original charges and their transposed placement on stores. -/
namespace ArtinMatthews
noncomputable section
open Filter
open scoped BigOperators

def markedRawEdgeChargedActualConstant (K : ℕ) (v₀ H W A L D G : ℝ) : ℝ :=
  (L*v₀^K)*(8*D*G)^K*H^2*(33*W*(8*A+5))

theorem markedRawEdgeCharged_actual_weighted_row_eventually
    {J : Type*} [Fintype J] [DecidableEq J] (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j) :
    ∀ᶠ x : ℝ in atTop, ∀ (pads B : ℕ) (Z : Finset (ℤ × ℤ))
      (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (δ γ : J → ℂ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
      (r d₀ Y Q q ρ H W A v₀ L D G : ℝ)
      (χ : MarkedRawState (markedRawActualPrimeBand e x) (pads+1) B Z → ℂ)
      (s : MarkedRawState (markedRawActualPrimeBand e x) (pads+1) B Z) (w : ℤ × ℤ)
      (modifier : MarkedRawEdgeChoice hZ s → ℂ),
      1 ≤ Y → 1 ≤ Q → 0 ≤ q → q ≤ 1 → 0 ≤ ρ → ρ ≤ 1 →
      0 ≤ H → 0 ≤ W → 0 ≤ A → 1 ≤ v₀ → 0 ≤ L → 1 ≤ D → 1 ≤ G →
      (∀ j,‖δ j‖ ≤ D) → (∀ j,‖γ j‖ ≤ G) →
      (∀ t,‖η t‖ ≤ H) → (∀ t,‖ψ t‖ ≤ W) → (∀ t,ψ t ≠ 0 → |t| ≤ A) →
      (∀ s,‖χ s‖ ≤ 1) → (∀ c,‖modifier c‖ ≤ L) →
      markedMinorIntegerDet s.1.1 w=1 → markedMinorIntegerTau r s.1.1 ≠ 0 →
      (∀ v ∈ Z,|markedMinorIntegerTau r v/markedMinorIntegerTau r s.1.1| ≤ 16) →
      markedRawEdgeChargedWeightedAbsRow (markedRawActualPrimeAtom e q x) δ γ hZ
        (markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ χ) v₀ s modifier ≤
        markedRawEdgeChargedActualConstant (Fintype.card J) v₀ H W A L D G*(B+1:ℝ)^(Fintype.card J)*Q^3 := by
  filter_upwards [markedDirty_actual_band_transfer_eventually e he,
    markedRawGhost_actual_band_mass_eventually e he] with x htransfer hmass
  intro pads B Z hZ δ γ ψ η r d₀ Y Q q ρ H W A v₀ L D G χ s w modifier
    hY hQ hq₀ hq₁ hρ₀ hρ₁ hH hW hA hv₀ hL hD hG hδ hγ hη hψ hsupp hχ hmodifier hw hτ hbox
  have hr := markedRawEdgeCharged_weighted_row_le_polynomial (markedRawActualPrimeAtom e q x) δ γ
    (htransfer q hq₀ hq₁).1 hD hG (by norm_num : (1:ℝ) ≤ 2) hδ hγ (hmass q hq₀ hq₁)
    hZ ψ η r d₀ Y Q ρ H W A v₀ hY hQ hA hρ₀ hρ₁ hH hW hv₀ hη hψ hsupp
    χ hχ s w hw hτ hbox modifier hL hmodifier
  exact hr.trans_eq (by unfold markedRawEdgeChargedActualConstant; ring)

theorem markedRawEdgeCharged_actual_original_row_eventually
    {J : Type*} [Fintype J] [DecidableEq J] (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j) :
    ∀ᶠ x : ℝ in atTop, ∀ (pads B : ℕ) (Z : Finset (ℤ × ℤ))
      (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
      (r d₀ Y Q q ρ H W A v₀ L : ℝ)
      (χ : MarkedRawState (markedRawActualPrimeBand e x) (pads+1) B Z → ℂ)
      (s : MarkedRawState (markedRawActualPrimeBand e x) (pads+1) B Z) (w : ℤ × ℤ)
      (modifier : MarkedRawEdgeChoice hZ s → ℂ),
      1 ≤ Y → 1 ≤ Q → 0 ≤ q → q ≤ 1 → 0 ≤ ρ → ρ ≤ 1 →
      0 ≤ H → 0 ≤ W → 0 ≤ A → 1 ≤ v₀ → 0 ≤ L →
      (∀ t,‖η t‖ ≤ H) → (∀ t,‖ψ t‖ ≤ W) → (∀ t,ψ t ≠ 0 → |t| ≤ A) →
      (∀ s,‖χ s‖ ≤ 1) → (∀ c,‖modifier c‖ ≤ L) →
      markedMinorIntegerDet s.1.1 w=1 → markedMinorIntegerTau r s.1.1 ≠ 0 →
      (∀ v ∈ Z,|markedMinorIntegerTau r v/markedMinorIntegerTau r s.1.1| ≤ 16) →
      markedRawEdgeChargedWeightedAbsRow (markedRawActualPrimeAtom e q x)
        (fun j => ((bandReciprocalMass (markedLogPowerBand (e j) x))⁻¹:ℝ)) (fun _ => 1) hZ
        (markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ χ) v₀ s modifier ≤
        markedRawEdgeCrudeActualConstant (Fintype.card J) v₀ H W A L*(B+1:ℝ)^(Fintype.card J)*Q^3 := by
  filter_upwards [markedRawEdgeCharged_actual_weighted_row_eventually e he,
    markedDirty_actual_band_transfer_eventually e he] with x hrow htransfer
  intro pads B Z hZ ψ η r d₀ Y Q q ρ H W A v₀ L χ s w modifier
    hY hQ hq₀ hq₁ hρ₀ hρ₁ hH hW hA hv₀ hL hη hψ hsupp hχ hmodifier hw hτ hbox
  have ht := htransfer q hq₀ hq₁
  have hδ : ∀ j,‖(((bandReciprocalMass (markedLogPowerBand (e j) x))⁻¹:ℝ):ℂ)‖ ≤ 2/Real.log 2 := by
    intro j
    rw [Complex.norm_real,Real.norm_of_nonneg (inv_pos.mpr (ht.2.1 j).1).le]
    exact (ht.2.1 j).2
  have hr := hrow pads B Z hZ _ (fun _ => 1) ψ η r d₀ Y Q q ρ H W A v₀ L
    (2/Real.log 2) 1 χ s w modifier hY hQ hq₀ hq₁ hρ₀ hρ₁ hH hW hA hv₀ hL
    markedDirty_transfer_constant_one_le le_rfl hδ (by intro j; simp) hη hψ hsupp hχ hmodifier hw hτ hbox
  apply hr.trans_eq
  unfold markedRawEdgeChargedActualConstant markedRawEdgeCrudeActualConstant
  rw [show 8*(2/Real.log 2)*1=(16/Real.log 2:ℝ) by ring]

/-- The genuine transposed charges and reversed physical kernel have the
same crude majorant; reflection changes neither cutoff norm nor support. -/
theorem markedRawEdgeCharged_actual_reverse_row_eventually
    {J : Type*} [Fintype J] [DecidableEq J] (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j)
    (hinj : Function.Injective e) :
    ∀ᶠ x : ℝ in atTop, ∀ (pads B : ℕ) (Z : Finset (ℤ × ℤ))
      (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
      (r d₀ Y Q q ρ H W A v₀ L : ℝ)
      (χ : MarkedRawState (markedRawActualPrimeBand e x) (pads+1) B Z → ℂ)
      (s : MarkedRawState (markedRawActualPrimeBand e x) (pads+1) B Z) (w : ℤ × ℤ)
      (modifier : MarkedRawEdgeChoice hZ s → ℂ),
      1 ≤ Y → 1 ≤ Q → 0 ≤ q → q ≤ 1 → 0 ≤ ρ → ρ ≤ 1 →
      0 ≤ H → 0 ≤ W → 0 ≤ A → 1 ≤ v₀ → 0 ≤ L →
      (∀ t,‖η t‖ ≤ H) → (∀ t,‖ψ t‖ ≤ W) → (∀ t,ψ t ≠ 0 → |t| ≤ A) →
      (∀ s,‖χ s‖ ≤ 1) → (∀ c,‖modifier c‖ ≤ L) →
      markedMinorIntegerDet s.1.1 w=1 → markedMinorIntegerTau r s.1.1 ≠ 0 →
      (∀ v ∈ Z,|markedMinorIntegerTau r v/markedMinorIntegerTau r s.1.1| ≤ 16) →
      markedRawEdgeChargedWeightedAbsRow (markedRawActualPrimeAtom e q x)
        (fun _ => 1) (fun j => ((bandReciprocalMass (markedLogPowerBand (e j) x))⁻¹:ℝ)) hZ
        (fun t u => markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ χ u t) v₀ s modifier ≤
        markedRawEdgeCrudeActualConstant (Fintype.card J) v₀ H W A L*(B+1:ℝ)^(Fintype.card J)*Q^3 := by
  filter_upwards [markedRawEdgeCharged_actual_weighted_row_eventually e he,
    markedDirty_actual_band_transfer_eventually e he,
    markedRawActualPrimeBand_disjoint_eventually e hinj] with x hrow htransfer hdisj
  intro pads B Z hZ ψ η r d₀ Y Q q ρ H W A v₀ L χ s w modifier
    hY hQ hq₀ hq₁ hρ₀ hρ₁ hH hW hA hv₀ hL hη hψ hsupp hχ hmodifier hw hτ hbox
  rw [markedRawEdgeChargedWeightedAbsRow_reverse_eq _ _ _ hdisj hZ ψ η d₀ Y Q ρ v₀ χ s modifier]
  have ht := htransfer q hq₀ hq₁
  have hγ : ∀ j,‖(((bandReciprocalMass (markedLogPowerBand (e j) x))⁻¹:ℝ):ℂ)‖ ≤ 2/Real.log 2 := by
    intro j
    rw [Complex.norm_real,Real.norm_of_nonneg (inv_pos.mpr (ht.2.1 j).1).le]
    exact (ht.2.1 j).2
  have hb := markedRawEdgeReflectedCutoff_bounds ψ hψ hsupp
  have hr := hrow pads B Z hZ (fun _ => 1) _ (markedRawEdgeReflectedCutoff ψ) η r d₀ Y Q q ρ H W A v₀ L
    1 (2/Real.log 2) χ s w modifier hY hQ hq₀ hq₁ hρ₀ hρ₁ hH hW hA hv₀ hL
    le_rfl markedDirty_transfer_constant_one_le (by intro j; simp) hγ hη hb.1 hb.2 hχ hmodifier hw hτ hbox
  apply hr.trans_eq
  unfold markedRawEdgeChargedActualConstant markedRawEdgeCrudeActualConstant
  rw [show 8*1*(2/Real.log 2)=(16/Real.log 2:ℝ) by ring]

end
end ArtinMatthews
