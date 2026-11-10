module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import OAI.NumberTheory.Jacobsthal.Sieve.ResidueFibres
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
public import OAI.NumberTheory.Jacobsthal.Partitions.StationaryFibres


set_option backward.privateInPublic true
@[expose] public section

namespace OAI

namespace Erdos970

section

namespace ErdosKloosterman.PrimePower

theorem standard_character_reduction (n d : ℕ) [NeZero n] [NeZero d]
    (x : ZMod (n*d)) :
    ZMod.stdAddChar ((n : ZMod (n*d)) * x) =
      ZMod.stdAddChar (reduction n d x) := by
  have hl : (n : ZMod (n*d)) * x =
      (((n : ℤ) * (x.val : ℤ) : ℤ) : ZMod (n*d)) := by
    push_cast
    rw [ZMod.natCast_zmod_val]
  have hr : reduction n d x = ((x.val : ℤ) : ZMod d) := by
    simpa only [Int.cast_natCast] using reduction_apply_val n d x
  rw [hl, hr, ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne n
  field_simp

theorem scaled_phase_reduction (n d : ℕ) [NeZero n] [NeZero d] (h k : ℤ)
    (u : (ZMod (n*d))ˣ) :
    ZMod.stdAddChar ((((n : ℤ)*h : ℤ) : ZMod (n*d)) * (u : ZMod (n*d)) +
      (((n : ℤ)*k : ℤ) : ZMod (n*d)) * (↑u⁻¹ : ZMod (n*d))) =
    ZMod.stdAddChar ((h : ZMod d) * (ZMod.unitsMap (dvd_mul_left d n) u : ZMod d) +
      (k : ZMod d) * (↑(ZMod.unitsMap (dvd_mul_left d n) u)⁻¹ : ZMod d)) := by
  have hphase : (((n : ℤ)*h : ℤ) : ZMod (n*d)) * (u : ZMod (n*d)) +
      (((n : ℤ)*k : ℤ) : ZMod (n*d)) * (↑u⁻¹ : ZMod (n*d)) =
      (n : ZMod (n*d)) * ((h : ZMod (n*d))*u + (k : ZMod (n*d))*↑u⁻¹) := by
    push_cast
    ring
  rw [hphase, standard_character_reduction]
  congr 1
  simp [reduction, ZMod.unitsMap_def, ← map_inv]

end ErdosKloosterman.PrimePower

end

end Erdos970

end OAI
