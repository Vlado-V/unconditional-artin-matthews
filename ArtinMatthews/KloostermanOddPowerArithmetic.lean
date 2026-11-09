module

public import ArtinMatthews.KloostermanCubicStationary
public import OAI.NumberTheory.Jacobsthal.Estimates.PrimitiveThreeQuarters
public import OAI.NumberTheory.Jacobsthal.Harmonic.CharacterReduction


set_option backward.privateInPublic true
@[expose] public section

/-! Exact prime-power nilpotence, stationary divisibility, and the genuine root-count input. -/
noncomputable section
open scoped BigOperators
open OAI.Erdos970.ErdosKloosterman OAI.Erdos970.ErdosKloosterman.PrimePower
namespace ArtinMatthews.PrimePowerWeil

attribute [local instance] Classical.decEq

abbrev OddPowerRing (p m : ℕ) := ZMod (p^(m+1)*p^m)

def oddPowerReduction (p m : ℕ) : OddPowerRing p m →+* ZMod p :=
  ZMod.castHom (dvd_mul_of_dvd_left (dvd_pow_self p (by omega : m+1≠0)) (p^m)) (ZMod p)

theorem oddPowerModulus_factor (p m : ℕ) : p^(m+1)*p^m=p^(2*m)*p := by
  rw [← pow_add,← pow_succ]
  congr 1
  omega

theorem oddPower_outer_square_zero (p m : ℕ) :
    ((p^(m+1):ℕ):OddPowerRing p m)^2=0 := by
  rw [← Nat.cast_pow,ZMod.natCast_eq_zero_iff,← pow_add,← pow_mul]
  exact pow_dvd_pow p (by omega)

theorem oddPower_inner_cube_zero (p m : ℕ) (hm : 1≤m) :
    ((p^m:ℕ):OddPowerRing p m)^3=0 := by
  rw [← Nat.cast_pow,ZMod.natCast_eq_zero_iff,← pow_add,← pow_mul]
  exact pow_dvd_pow p (by omega)

theorem oddPower_outer_mul_inner_zero (p m : ℕ) :
    ((p^(m+1):ℕ):OddPowerRing p m)*((p^m:ℕ):OddPowerRing p m)=0 := by
  rw [← Nat.cast_mul,ZMod.natCast_self]

theorem oddPower_inner_square (p m : ℕ) :
    ((p^m:ℕ):OddPowerRing p m)^2=((p^(2*m):ℕ):OddPowerRing p m) := by
  rw [← Nat.cast_pow,← pow_mul]
  congr 2
  omega

theorem oddPower_stationary_divisibility (p m : ℕ) [Fact p.Prime]
    (a b : OddPowerRing p m) (u : (OddPowerRing p m)ˣ)
    (hu : u∈stationaryUnits ((p^(m+1):ℕ):OddPowerRing p m) a b) :
    p^m∣(a-b*(↑u⁻¹:OddPowerRing p m)^2).val := by
  have hzero : ((p^(m+1):ℕ):OddPowerRing p m)*(a-b*(↑u⁻¹:OddPowerRing p m)^2)=0 :=
    by simpa only [stationaryUnits,Finset.mem_filter,Finset.mem_univ,true_and] using hu
  exact (ZMod.natCast_eq_zero_iff _ _).mp
    ((mul_annihilator_iff (p^(m+1)) (p^m) (pow_pos (Fact.out : p.Prime).pos _) _).mp hzero)

theorem oddPower_stationary_derivative_factor (p m : ℕ) [Fact p.Prime]
    (a b : OddPowerRing p m) (u : (OddPowerRing p m)ˣ)
    (hu : u∈stationaryUnits ((p^(m+1):ℕ):OddPowerRing p m) a b) :
    a-b*(↑u⁻¹:OddPowerRing p m)^2=
      ((p^m:ℕ):OddPowerRing p m)*
        (((a-b*(↑u⁻¹:OddPowerRing p m)^2).val/p^m:ℕ):OddPowerRing p m) := by
  have hd := oddPower_stationary_divisibility p m a b u hu
  rw [← Nat.cast_mul,Nat.mul_div_cancel' hd,ZMod.natCast_zmod_val]

theorem oddPower_stationary_card (p m : ℕ) [Fact p.Prime] (hm : 0<m) (hp2 : p≠2)
    (h k : ℤ) (hh : (h:ZMod p)≠0) :
    (stationaryUnits ((p^(m+1):ℕ):OddPowerRing p m) (h:OddPowerRing p m) k).card≤2*p^(m+1) := by
  have hc := stationary_card_le_root_card_mul (p^(m+1)) (p^m)
    (h:OddPowerRing p m) (k:OddPowerRing p m)
  have hr : (quadraticUnitRoots (p^m)
      (reduction (p^(m+1)) (p^m) (h:OddPowerRing p m))
      (reduction (p^(m+1)) (p^m) (k:OddPowerRing p m))).card≤2 := by
    simpa only [map_intCast] using quadraticUnitRoots_card_le_two p m hm hp2
      (h:ZMod (p^m)) (k:ZMod (p^m)) (int_frequency_isUnit p m hm h hh)
  exact hc.trans (Nat.mul_le_mul_right (p^(m+1)) hr)

end ArtinMatthews.PrimePowerWeil
