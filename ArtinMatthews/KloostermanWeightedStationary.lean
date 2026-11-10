module

public import OAI.NumberTheory.Jacobsthal.Harmonic.StationaryPhase
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
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

/-! Weighted extension of the exact finite-ring stationary-phase identity
from OAI.NumberTheory.Jacobsthal.Harmonic.StationaryPhase. The shift units,
shift equivalence and phase algebra are reused directly. The extra weight
is required to be invariant under the same square-zero translations. -/

namespace ArtinMatthews
open scoped BigOperators
open OAI.Erdos970.ErdosKloosterman
open OAI.Erdos970.ErdosKloosterman.PrimePower

noncomputable section
variable {R : Type*} [CommRing R] [Fintype R]
attribute [local instance] Classical.decEq

/-- The actual weighted complete sum over units. -/
def weightedKloosterman (ψ : AddChar R ℂ) (W : Rˣ → ℂ) (a b : R) : ℂ :=
  ∑ u : Rˣ, W u * ψ (a*(u : R)+b*(↑u⁻¹ : R))

theorem weightedKloosterman_shift (ψ : AddChar R ℂ) (W : Rˣ → ℂ)
    (a b q : R) (hq : q^2=0)
    (hW : ∀ (u : Rˣ) (z : R), W (shiftUnit u (q*z) (by rw [mul_pow,hq,zero_mul])) = W u)
    (z : R) :
    weightedKloosterman ψ W a b = ∑ u : Rˣ,
      (W u * ψ (a*(u : R)+b*(↑u⁻¹ : R))) *
        ψ (z*(q*(a-b*(↑u⁻¹ : R)^2))) := by
  have ht : (q*z)^2=0 := by rw [mul_pow,hq,zero_mul]
  have he := Equiv.sum_comp (shiftEquiv (q*z) ht)
    (fun u : Rˣ => W u * ψ (a*(u : R)+b*(↑u⁻¹ : R)))
  unfold weightedKloosterman
  rw [← he]
  apply Finset.sum_congr rfl
  intro u _
  change W (shiftUnit u (q*z) ht) *
    ψ (a*(shiftUnit u (q*z) ht : R)+b*(↑(shiftUnit u (q*z) ht)⁻¹ : R)) = _
  rw [hW, phase_shift, AddChar.map_add_eq_mul]
  have heq : (q*z)*(a-b*(↑u⁻¹ : R)^2) = z*(q*(a-b*(↑u⁻¹ : R)^2)) := by ring
  rw [heq]
  ring

/-- Exact stationary projection for an invariant weight. -/
theorem weightedKloosterman_stationary (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive)
    (W : Rˣ → ℂ) (a b q : R) (hq : q^2=0)
    (hW : ∀ (u : Rˣ) (z : R), W (shiftUnit u (q*z) (by rw [mul_pow,hq,zero_mul])) = W u) :
    weightedKloosterman ψ W a b = ∑ u ∈ stationaryUnits q a b,
      W u * ψ (a*(u : R)+b*(↑u⁻¹ : R)) := by
  classical
  have hcard : (Fintype.card R : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  apply mul_left_cancel₀ hcard
  calc
    _ = ∑ _z : R, weightedKloosterman ψ W a b := by simp
    _ = ∑ z : R, ∑ u : Rˣ,
        (W u * ψ (a*(u : R)+b*(↑u⁻¹ : R))) *
          ψ (z*(q*(a-b*(↑u⁻¹ : R)^2))) := by
      apply Finset.sum_congr rfl
      intro z _
      exact weightedKloosterman_shift ψ W a b q hq hW z
    _ = ∑ u : Rˣ, (W u * ψ (a*(u : R)+b*(↑u⁻¹ : R))) *
        (∑ z : R, ψ (z*(q*(a-b*(↑u⁻¹ : R)^2)))) := by
      rw [Finset.sum_comm]
      simp_rw [Finset.mul_sum]
    _ = _ := by
      simp_rw [AddChar.sum_mulShift _ hψ]
      rw [Finset.mul_sum]
      simp [stationaryUnits, Finset.sum_filter, mul_comm]

/-- A residue restriction constant on the actual stationary support can
be extracted as a scalar from the full ordinary Kloosterman sum. -/
theorem weightedKloosterman_eq_scalar (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive)
    (W : Rˣ → ℂ) (a b q : R) (hq : q^2=0) (C : ℂ)
    (hW : ∀ (u : Rˣ) (z : R), W (shiftUnit u (q*z) (by rw [mul_pow,hq,zero_mul])) = W u)
    (hC : ∀ u ∈ stationaryUnits q a b, W u = C) :
    weightedKloosterman ψ W a b = C * sum ψ a b := by
  rw [weightedKloosterman_stationary ψ hψ W a b q hq hW,
    stationary_phase_identity ψ hψ a b q hq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  rw [hC u hu]

end
end ArtinMatthews
