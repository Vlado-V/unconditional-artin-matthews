module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.NumberTheory.Jacobsthal.Sieve.ResidueFibres
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

namespace OAI

namespace Erdos970

section

namespace ErdosKloosterman.PrimePower

attribute [local instance] Classical.decEq

theorem reduction_apply_val (n d : ℕ) [NeZero n] [NeZero d] (x : ZMod (n*d)) :
    reduction n d x = (x.val : ZMod d) := by
  nth_rw 1 [← x.natCast_zmod_val]
  simp [reduction]

noncomputable def quadraticUnitRoots (d : ℕ) [NeZero d] (a b : ZMod d) : Finset (ZMod d) :=
  Finset.univ.filter fun x => IsUnit x ∧ a * x^2 = b

theorem mem_stationary_iff_reduction (n d : ℕ) [NeZero n] [NeZero d]
    (a b : ZMod (n*d)) (u : (ZMod (n*d))ˣ) :
    u ∈ stationaryUnits (n : ZMod (n*d)) a b ↔
      reduction n d (u : ZMod (n*d)) ∈
        quadraticUnitRoots d (reduction n d a) (reduction n d b) := by
  have hu : IsUnit (reduction n d (u : ZMod (n*d))) :=
    (u.isUnit).map (reduction n d)
  simp only [stationaryUnits, Finset.mem_filter, Finset.mem_univ, true_and,
    quadraticUnitRoots, hu]
  rw [stationary_iff_quadratic, mul_annihilator_iff n d (NeZero.pos n),
    ← reduction_apply_val]
  simp only [map_sub, map_mul, map_pow, sub_eq_zero]

theorem stationary_card_le_root_card_mul (n d : ℕ) [NeZero n] [NeZero d]
    (a b : ZMod (n*d)) :
    (stationaryUnits (n : ZMod (n*d)) a b).card ≤
      (quadraticUnitRoots d (reduction n d a) (reduction n d b)).card * n := by
  let S := quadraticUnitRoots d (reduction n d a) (reduction n d b)
  rw [← reduction_preimage_card n d S]
  apply Finset.card_le_card_of_injOn (fun u : (ZMod (n*d))ˣ => (u : ZMod (n*d)))
  · intro u hu
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (mem_stationary_iff_reduction n d a b u).mp hu⟩
  · intro u _ v _ huv
    exact Units.val_injective huv

end ErdosKloosterman.PrimePower

end

end Erdos970

end OAI
