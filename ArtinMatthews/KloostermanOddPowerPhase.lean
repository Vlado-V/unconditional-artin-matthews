module

public import ArtinMatthews.KloostermanOddPowerArithmetic
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
public import OAI.NumberTheory.Jacobsthal.Harmonic.CharacterReduction


set_option backward.privateInPublic true
@[expose] public section

/-! The actual second-order prime-power phase is an affine quadratic phase modulo p. -/
noncomputable section
open scoped BigOperators
open OAI.Erdos970.ErdosKloosterman OAI.Erdos970.ErdosKloosterman.PrimePower
namespace ArtinMatthews.PrimePowerWeil

attribute [local instance] Classical.decEq

theorem stdAddChar_factor_transport (N n d : ℕ) [NeZero N] [NeZero n] [NeZero d]
    (hN : N=n*d) (hd : d∣N) (x : ZMod N) :
    ZMod.stdAddChar ((n:ZMod N)*x)=ZMod.stdAddChar (ZMod.castHom hd (ZMod d) x) := by
  subst N
  exact standard_character_reduction n d x

theorem oddPower_stdAddChar_factor (p m : ℕ) [Fact p.Prime] (x : OddPowerRing p m) :
    ZMod.stdAddChar (((p^(2*m):ℕ):OddPowerRing p m)*x)=
      ZMod.stdAddChar (oddPowerReduction p m x) := by
  exact stdAddChar_factor_transport _ (p^(2*m)) p (oddPowerModulus_factor p m) _ x

theorem oddPower_phase_reduction (p m : ℕ) [Fact p.Prime]
    (a b : OddPowerRing p m) (u : (OddPowerRing p m)ˣ)
    (hu : u∈stationaryUnits ((p^(m+1):ℕ):OddPowerRing p m) a b) (z : ZMod p) :
    ZMod.stdAddChar
      ((((p^m:ℕ):OddPowerRing p m)*(z.val:OddPowerRing p m))*(a-b*(↑u⁻¹:OddPowerRing p m)^2)+
        (((p^m:ℕ):OddPowerRing p m)*(z.val:OddPowerRing p m))^2*(b*(↑u⁻¹:OddPowerRing p m)^3)) =
      ZMod.stdAddChar (oddPowerReduction p m (b*(↑u⁻¹:OddPowerRing p m)^3)*z^2+
        (((a-b*(↑u⁻¹:OddPowerRing p m)^2).val/p^m:ℕ):ZMod p)*z) := by
  let δ : ℕ := (a-b*(↑u⁻¹:OddPowerRing p m)^2).val/p^m
  have hphase :
      ((((p^m:ℕ):OddPowerRing p m)*(z.val:OddPowerRing p m))*(a-b*(↑u⁻¹:OddPowerRing p m)^2)+
        (((p^m:ℕ):OddPowerRing p m)*(z.val:OddPowerRing p m))^2*(b*(↑u⁻¹:OddPowerRing p m)^3)) =
      ((p^(2*m):ℕ):OddPowerRing p m)*((δ:OddPowerRing p m)*(z.val:OddPowerRing p m)+
        (b*(↑u⁻¹:OddPowerRing p m)^3)*(z.val:OddPowerRing p m)^2) := by
    rw [oddPower_stationary_derivative_factor p m a b u hu]
    rw [← oddPower_inner_square]
    dsimp only [δ]
    ring
  rw [hphase,oddPower_stdAddChar_factor]
  congr 1
  simp only [map_add,map_mul,map_pow,map_natCast,ZMod.natCast_zmod_val]
  ring

theorem oddPower_stationary_reduction_zero (p m : ℕ) [Fact p.Prime] (hm : 1≤m)
    (a b : OddPowerRing p m) (u : (OddPowerRing p m)ˣ)
    (hu : u∈stationaryUnits ((p^(m+1):ℕ):OddPowerRing p m) a b) :
    oddPowerReduction p m (a-b*(↑u⁻¹:OddPowerRing p m)^2)=0 := by
  let D := a-b*(↑u⁻¹:OddPowerRing p m)^2
  have hd : p∣D.val := (dvd_pow_self p (by omega : m≠0)).trans
    (oddPower_stationary_divisibility p m a b u hu)
  have he : oddPowerReduction p m D=(D.val:ZMod p) := by
    nth_rw 1 [← D.natCast_zmod_val]
    exact map_natCast _ _
  rw [he]
  exact (ZMod.natCast_eq_zero_iff _ _).mpr hd

theorem oddPower_stationary_quadratic_ne_zero (p m : ℕ) [Fact p.Prime] (hm : 1≤m)
    (a b : OddPowerRing p m) (ha : oddPowerReduction p m a≠0) (u : (OddPowerRing p m)ˣ)
    (hu : u∈stationaryUnits ((p^(m+1):ℕ):OddPowerRing p m) a b) :
    oddPowerReduction p m (b*(↑u⁻¹:OddPowerRing p m)^3)≠0 := by
  have hD := oddPower_stationary_reduction_zero p m hm a b u hu
  have hb : oddPowerReduction p m b≠0 := by
    intro hb
    exact ha (by simpa only [map_sub,map_mul,map_pow,hb,zero_mul,sub_zero] using hD)
  have hi : oddPowerReduction p m (↑u⁻¹:OddPowerRing p m)≠0 :=
    isUnit_iff_ne_zero.mp ((u⁻¹).isUnit.map (oddPowerReduction p m))
  rw [map_mul,map_pow]
  exact mul_ne_zero hb (pow_ne_zero 3 hi)

end ArtinMatthews.PrimePowerWeil
