module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.NumberTheory.JointDickman.Amplification.OscillatoryTests
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import OAI.NumberTheory.JointDickman.Amplification.RamanujanRoots


set_option backward.privateInPublic true
@[expose] public section

namespace OAI

/-! # Relating real exponential notation to residue characters -/

namespace JointDickman

theorem additivePhase_add (s t : ℝ) :
    additivePhase (s + t) = additivePhase s * additivePhase t := by
  unfold additivePhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem stdAddChar_as_additivePhase {q : ℕ} [NeZero q] (n : ℕ) :
    ZMod.stdAddChar (n : ZMod q) = additivePhase ((n : ℝ) / q) := by
  rw [stdAddChar_natCast]
  unfold additivePhase
  congr 1
  push_cast
  ring

theorem unit_nat_phase {q : ℕ} [NeZero q] (u : (ZMod q)ˣ) (n : ℕ) :
    ZMod.stdAddChar ((u : ZMod q) * (n : ZMod q)) =
      additivePhase (((u : ZMod q).val : ℝ) * n / q) := by
  conv_lhs => rw [← ZMod.natCast_zmod_val (u : ZMod q), ← Nat.cast_mul, stdAddChar_as_additivePhase]
  push_cast
  rfl

end JointDickman

end OAI
