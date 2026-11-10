module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.NumberTheory.Jacobsthal.Estimates.PairCollisionCount
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
public import OAI.NumberTheory.Jacobsthal.Harmonic.KloostermanCRTCharacter


set_option backward.privateInPublic true
@[expose] public section

namespace OAI

namespace Erdos970

section

namespace ErdosKloosterman

attribute [local instance] Classical.decEq

theorem sum_mulShift {R : Type*} [CommRing R] [Fintype R]
    (ψ : AddChar R ℂ) (r a b : R) :
    sum (ψ.mulShift r) a b = sum ψ (r*a) (r*b) := by
  unfold sum
  apply Finset.sum_congr rfl
  intro u _
  rw [AddChar.mulShift_apply]
  congr 1
  ring

theorem standardSum_crt (m n : ℕ) [NeZero m] [NeZero n] (hmn : m.Coprime n)
    (h k : ℤ) :
    standardSum (m*n) h k =
      standardSum m (Nat.gcdB m n * h) (Nat.gcdB m n * k) *
        standardSum n (Nat.gcdA m n * h) (Nat.gcdA m n * k) := by
  unfold standardSum
  rw [stdAddChar_crt m n hmn, sum_product_ringEquiv]
  simp only [map_intCast, Prod.fst_intCast, Prod.snd_intCast, sum_mulShift,
    Int.cast_mul]

theorem norm_standardSum_crt (m n : ℕ) [NeZero m] [NeZero n] (hmn : m.Coprime n)
    (h k : ℤ) :
    ‖standardSum (m*n) h k‖ =
      ‖standardSum m (Nat.gcdB m n * h) (Nat.gcdB m n * k)‖ *
        ‖standardSum n (Nat.gcdA m n * h) (Nat.gcdA m n * k)‖ := by
  rw [standardSum_crt m n hmn, norm_mul]

end ErdosKloosterman

end

end Erdos970

end OAI
