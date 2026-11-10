module

public import ArtinMatthews.CircleDetector
public import ArtinMatthews.DoubleVoronoiDetection
public import Mathlib.RingTheory.SimpleRing.Principal


set_option backward.privateInPublic true
@[expose] public section

/-! Compatibility of the integer-frequency circle approximation with the
exact normalized d-congruence detector used by double Voronoi summation. -/

noncomputable section
open scoped BigOperators
open OAI.Erdos970.ErdosKloosterman.PrimePower
namespace ArtinMatthews

theorem circle_residue_average (d : ℕ) [NeZero d] (x : ZMod d) :
    (∑ j : ZMod d, ZMod.stdAddChar (j*x))/(d : ℂ) =
      if x=0 then 1 else 0 := by
  rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar d)]
  simp only [ZMod.card]
  split_ifs <;> simp [show (d : ℂ)≠0 by exact_mod_cast NeZero.ne d]

theorem circle_lifted_congruence_average (H d : ℕ) [NeZero H] [NeZero d]
    (a : (ZMod (H*d))ˣ) (n x : ℤ) :
    (∑ j : ZMod d, ZMod.stdAddChar
      ((a : ZMod (H*d))*(n : ZMod (H*d)) +
        (H : ZMod (H*d))*(j.val : ZMod (H*d))*(x : ZMod (H*d))))/(d : ℂ) =
      ZMod.stdAddChar ((a : ZMod (H*d))*(n : ZMod (H*d))) *
        (if (d : ℤ)∣x then 1 else 0) := by
  classical
  simp_rw [doubleVoronoi_lifted_character]
  have hred : reduction H d (x : ZMod (H*d)) = (x : ZMod d) := map_intCast _ _
  simp_rw [hred]
  rw [← Finset.mul_sum,mul_div_assoc,circle_residue_average]
  simp only [ZMod.intCast_zmod_eq_zero_iff_dvd]

theorem circle_with_congruence_exact (H d : ℕ) [NeZero H] [NeZero d]
    (n x : ℤ) :
    (∑ a : (ZMod (H*d))ˣ, ∑ j : ZMod d, ZMod.stdAddChar
      ((a : ZMod (H*d))*(n : ZMod (H*d)) +
        (H : ZMod (H*d))*(j.val : ZMod (H*d))*(x : ZMod (H*d))))/(d : ℂ) =
      primitiveCircleSum (H*d) n * (if (d : ℤ)∣x then 1 else 0) := by
  classical
  rw [Finset.sum_div]
  simp_rw [circle_lifted_congruence_average]
  rw [← Finset.sum_mul,primitiveCircleSum_eq]
  congr 1
  unfold OAI.JointDickman.ramanujanSum
  apply Finset.sum_congr rfl
  intro a _ha
  congr 1
  ring

end ArtinMatthews
