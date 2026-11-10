module

public import ArtinMatthews.MarkedMinorArcRawGhostChoiceCauchy
public import ArtinMatthews.MarkedMinorArcRawMemoryAmbient
public import ArtinMatthews.MarkedChoiceModifierCauchy
public import ArtinMatthews.MarkedEstimateMertensBands
public import ArtinMatthews.MarkedMinorArcRawGhostEnergyColumn
public import ArtinMatthews.MarkedMinorArcRawGhostSwappedRow
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
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

/-! Bounded literal birth-choice multipliers use the genuine absolute
ghost Schur rows. This supplies a fixed crude ghost constant while leaving
the separate old-memory equivariance obligation explicit. -/

noncomputable section
namespace ArtinMatthews
open Filter
open scoped BigOperators

def markedRawGhostModifiedApply {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    (qStage ρ : ℝ) {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (modifier : (s : MarkedRawState P M B Z) → MarkedMemoryGhostChoice hZ s → ℂ)
    (f : MarkedRawState P M B Z → ℂ) (s : MarkedRawState P M B Z) : ℂ :=
  ∑ c : MarkedMemoryGhostChoice hZ s, markedMemoryGhostChoiceWeight ν V qStage ρ hZ s c *
    (modifier s c*f (markedMemoryGhostChoiceTarget hZ s c))

theorem markedRawGhostModifiedApply_choice_cauchy {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    (qStage ρ : ℝ) {v₀ : ℝ} (hv₀ : 0 < v₀) {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (modifier : (s : MarkedRawState P M B Z) → MarkedMemoryGhostChoice hZ s → ℂ)
    (f : MarkedRawState P M B Z → ℂ) (s : MarkedRawState P M B Z)
    (hm : ∀ c, ‖modifier s c‖ ≤ 1) :
    ‖markedRawGhostModifiedApply ν V qStage ρ hZ modifier f s‖^2 ≤
      markedRawGhostWeightedAbsRow ν V qStage ρ v₀ s.2.2 s.1.1 (hZ _ s.1.2)*
        markedRawGhostChoiceReverseEnergy ν V qStage ρ v₀ hZ f s := by
  classical
  have hs := markedChoiceModifier_finite_cauchy
    (markedMemoryGhostChoiceWeight ν V qStage ρ hZ s)
    (fun c => f (markedMemoryGhostChoiceTarget hZ s c)) (modifier s)
    (fun c => markedRawMemorySchurWeight v₀ (markedMemoryGhostChoiceTarget hZ s c).2.2 /
      markedRawMemorySchurWeight v₀ s.2.2)
    (fun _ => div_pos (markedRawMemorySchurWeight_pos hv₀ _) (markedRawMemorySchurWeight_pos hv₀ _)) hm
  rw [markedMemoryGhostChoice_abs_weighted_sum] at hs
  convert hs using 1
  congr 1
  unfold markedRawGhostChoiceReverseEnergy
  congr 1
  apply Finset.sum_congr rfl
  intro c _
  field_simp [(markedRawMemorySchurWeight_pos hv₀ s.2.2).ne',
    (markedRawMemorySchurWeight_pos hv₀ (markedMemoryGhostChoiceTarget hZ s c).2.2).ne']

theorem markedRawGhostModifiedApply_actual_energy_eventually
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j, (1/10:ℝ) ≤ e j) {q ρ : ℝ}
    (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) (hρ : 0 < ρ) (hgap : Real.sqrt q < ρ^2) :
    ∀ᶠ x : ℝ in atTop, ∀ qStage : ℝ, 0 ≤ qStage → qStage ≤ Real.sqrt q →
      ∀ (M B : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
        (modifier : (s : MarkedRawState (markedRawActualPrimeBand e x) M B Z) →
          MarkedMemoryGhostChoice hZ s → ℂ)
        (f : MarkedRawState (markedRawActualPrimeBand e x) M B Z → ℂ),
      (∀ s c, ‖modifier s c‖ ≤ 1) →
      (∀ z a, MarkedRawMemorySymmetric (fun m => f (z,(a,m)))) →
      (∑ s, markedRawStateMass (markedRawActualPrimeAtom e q x) s *
        ‖markedRawGhostModifiedApply (markedRawActualPrimeAtom e q x)
          (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) qStage ρ hZ modifier f s‖^2) ≤
        (Real.exp ((Fintype.card J:ℝ)*(2*markedRawGhostSchurParameter q ρ/ρ)))^2 *
          ∑ s, markedRawStateMass (markedRawActualPrimeAtom e q x) s*‖f s‖^2 := by
  classical
  have hV := eventually_all.mpr (fun j => marked_log_power_band_mass_eventually
    (show 0 < e j by linarith [he j]))
  filter_upwards [markedRawGhost_actual_weighted_row_eventually e he hq₀ hq₁ hρ hgap,
    markedRawGhostSwapped_actual_weighted_row_eventually e he hq₀ hq₁ hρ hgap,
    marked_actual_tilted_atom_comparison_eventually e he,hV] with x hrow hcolumn hν hV
  intro qStage hqs₀ hqs M B Z hZ modifier f hm hf
  let C := Real.exp ((Fintype.card J:ℝ)*(2*markedRawGhostSchurParameter q ρ/ρ))
  let v₀ := markedRawGhostSchurParameter q ρ
  have hC : 0 ≤ C := (Real.exp_pos _).le
  have hv₀ : 0 < v₀ := zero_lt_one.trans_le (markedRawGhostSchurParameter_ge_one q ρ)
  have hνpos : ∀ j p, 0 ≤ markedRawActualPrimeAtom e q x j p := by
    intro j p
    rw [markedRawActualPrimeAtom_eq_tilted]
    exact (hν q hq₀ hq₁ j _).1
  have hVp : ∀ j, 0 ≤ bandReciprocalMass (markedLogPowerBand (e j) x) :=
    fun j => ((by positivity : 0 < Real.log 2/2).trans (hV j).1).le
  have hsqrt : Real.sqrt q ≤ 1 := by nlinarith [Real.sq_sqrt hq₀,Real.sqrt_nonneg q]
  have heq := markedRawGhostChoiceReverseEnergy_sum_eq_swapped_row
    (markedRawActualPrimeAtom e q x) hνpos
    (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) hVp
    hqs₀ (hqs.trans hsqrt) hρ hv₀ hZ f hf
  calc
    _ ≤ C * ∑ s, markedRawStateMass (markedRawActualPrimeAtom e q x) s *
        markedRawGhostChoiceReverseEnergy (markedRawActualPrimeAtom e q x)
          (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) qStage ρ v₀ hZ f s := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro s _
      have hp := markedRawGhostModifiedApply_choice_cauchy (markedRawActualPrimeAtom e q x)
        (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) qStage ρ hv₀ hZ modifier f s (hm s)
      have hrev := markedRawGhostChoiceReverseEnergy_nonneg (markedRawActualPrimeAtom e q x)
        (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) qStage ρ hv₀ hZ f s
      have hb := mul_le_mul_of_nonneg_right (hrow qStage hqs₀ hqs B s.2.2 s.1.1 (hZ _ s.1.2)) hrev
      exact (mul_le_mul_of_nonneg_left (hp.trans hb) (markedRawStateMass_nonneg _ hνpos s)).trans_eq (by ring)
    _ = C * ∑ s, markedRawStateMass (markedRawActualPrimeAtom e q x) s*‖f s‖^2 *
        markedRawGhostSwappedWeightedAbsRow (markedRawActualPrimeAtom e q x)
          (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) qStage ρ v₀ s.2.2 s.1.1 (hZ _ s.1.2) := by
      rw [heq]
    _ ≤ C * (C * ∑ s, markedRawStateMass (markedRawActualPrimeAtom e q x) s*‖f s‖^2) := by
      apply mul_le_mul_of_nonneg_left _ hC
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro s _
      exact (mul_le_mul_of_nonneg_left (hcolumn qStage hqs₀ hqs B s.2.2 s.1.1 (hZ _ s.1.2))
        (mul_nonneg (markedRawStateMass_nonneg _ hνpos s) (sq_nonneg _))).trans_eq (by ring)
    _ = _ := by change C*(C*_) = C^2*_; ring

end ArtinMatthews
