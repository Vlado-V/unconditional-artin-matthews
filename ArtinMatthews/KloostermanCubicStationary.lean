module

public import ArtinMatthews.KloostermanCubicShift
public import OAI.NumberTheory.Jacobsthal.Harmonic.StationaryPhase
public import Mathlib.Tactic.Basify
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
public import OAI.NumberTheory.Jacobsthal.Primes.PrimePowerStationarity


set_option backward.privateInPublic true
@[expose] public section

/-! Exact cubic-shift averaging on the genuine first-order stationary support. -/
noncomputable section
open scoped BigOperators
open OAI.Erdos970.ErdosKloosterman OAI.Erdos970.ErdosKloosterman.PrimePower
namespace ArtinMatthews.PrimePowerWeil

variable {R : Type*} [CommRing R] [Fintype R]

theorem cubicShift_stationary_mem (q a b : R) (u : Rˣ) (t : R)
    (ht : t^3=0) (hqt : q*t=0) :
    cubicShiftUnit u t ht∈stationaryUnits q a b ↔ u∈stationaryUnits q a b := by
  classical
  simp only [stationaryUnits,Finset.mem_filter,Finset.mem_univ,true_and]
  rw [stationary_iff_quadratic,stationary_iff_quadratic,cubicShift_stationary_quadratic q a b u t ht hqt]

theorem stationary_cubic_shift_sum (ψ : AddChar R ℂ) (q a b t : R)
    (ht : t^3=0) (hqt : q*t=0) :
    (∑ u ∈ stationaryUnits q a b, ψ (a*(u:R)+b*(↑u⁻¹:R))) =
      ∑ u ∈ stationaryUnits q a b, ψ (a*(u:R)+b*(↑u⁻¹:R))*
        ψ (t*(a-b*(↑u⁻¹:R)^2)+t^2*(b*(↑u⁻¹:R)^3)) := by
  classical
  let S := stationaryUnits q a b
  let F : Rˣ → ℂ := fun u => ψ (a*(u:R)+b*(↑u⁻¹:R))
  have he := Equiv.sum_comp (cubicShiftEquiv t ht) (fun u : Rˣ => if u∈S then F u else 0)
  calc
    _ = ∑ u : Rˣ, if u∈S then F u else 0 := by simp [S,F,stationaryUnits,Finset.sum_filter]
    _ = ∑ u : Rˣ, if cubicShiftUnit u t ht∈S then F (cubicShiftUnit u t ht) else 0 := he.symm
    _ = ∑ u : Rˣ, if u∈S then F u*
        ψ (t*(a-b*(↑u⁻¹:R)^2)+t^2*(b*(↑u⁻¹:R)^3)) else 0 := by
      apply Finset.sum_congr rfl
      intro u _
      have hm : cubicShiftUnit u t ht∈S ↔ u∈S := cubicShift_stationary_mem q a b u t ht hqt
      by_cases hu : u∈S
      · rw [ite_eq_left (hm.mpr hu),ite_eq_left hu]
        unfold F
        rw [cubicShift_phase]
        have hp : a*(u:R)+b*(↑u⁻¹:R)+t*(a-b*(↑u⁻¹:R)^2)+t^2*(b*(↑u⁻¹:R)^3) =
            (a*(u:R)+b*(↑u⁻¹:R))+(t*(a-b*(↑u⁻¹:R)^2)+t^2*(b*(↑u⁻¹:R)^3)) := by ring
        rw [hp,AddChar.map_add_eq_mul]
      · rw [ite_eq_right (fun h => hu (hm.mp h)),ite_eq_right hu]
    _ = _ := by simp [S,F,stationaryUnits,Finset.sum_filter]

theorem kloosterman_cubic_stationary_shift (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive)
    (q₀ q a b : R) (hq₀ : q₀^2=0) (hq : q^3=0) (hqq : q₀*q=0) (z : R) :
    sum ψ a b = ∑ u ∈ stationaryUnits q₀ a b, ψ (a*(u:R)+b*(↑u⁻¹:R))*
      ψ ((q*z)*(a-b*(↑u⁻¹:R)^2)+(q*z)^2*(b*(↑u⁻¹:R)^3)) := by
  rw [stationary_phase_identity ψ hψ a b q₀ hq₀]
  exact stationary_cubic_shift_sum ψ q₀ a b (q*z)
    (by rw [mul_pow,hq,zero_mul]) (by rw [← mul_assoc,hqq,zero_mul])

theorem kloosterman_cubic_stationary_average {Z : Type*} [Fintype Z]
    (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) (q₀ q a b : R)
    (hq₀ : q₀^2=0) (hq : q^3=0) (hqq : q₀*q=0) (lift : Z → R) :
    (Fintype.card Z:ℂ)*sum ψ a b =
      ∑ u ∈ stationaryUnits q₀ a b, ψ (a*(u:R)+b*(↑u⁻¹:R))*
        ∑ z : Z, ψ ((q*lift z)*(a-b*(↑u⁻¹:R)^2)+(q*lift z)^2*(b*(↑u⁻¹:R)^3)) := by
  calc
    _ = ∑ _z : Z, sum ψ a b := by simp
    _ = ∑ z : Z, ∑ u ∈ stationaryUnits q₀ a b, ψ (a*(u:R)+b*(↑u⁻¹:R))*
        ψ ((q*lift z)*(a-b*(↑u⁻¹:R)^2)+(q*lift z)^2*(b*(↑u⁻¹:R)^3)) := by
      apply Finset.sum_congr rfl
      intro z _
      exact kloosterman_cubic_stationary_shift ψ hψ q₀ q a b hq₀ hq hqq (lift z)
    _ = _ := by
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum]

end ArtinMatthews.PrimePowerWeil
