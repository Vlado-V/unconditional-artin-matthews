module

public import Mathlib.Algebra.Group.Idempotent
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

/-!
# Units lift through finite commutative rings

A positive idempotent power of a preimage separates the component where its
image is a unit. Replacing the complementary component by one gives an actual
unit preimage. This applies to the finite ideal quotient maps used by the
cubic-theta residue-character construction.
-/

namespace ArtinMatthews

/-- Equal powers at two distinct exponents give a positive idempotent power. -/
theorem exists_positive_idempotent_pow_of_eq {M : Type*} [Monoid M]
    (x : M) {i j : ℕ} (hij : i < j) (hpow : x ^ i = x ^ j) :
    ∃ n : ℕ, 0 < n ∧ IsIdempotentElem (x ^ n) := by
  let d := j - i
  have hd : 0 < d := Nat.sub_pos_of_lt hij
  have hstep : x ^ (i + d) = x ^ i := by
    simpa only [d, Nat.add_sub_of_le hij.le] using hpow.symm
  have hiter (k : ℕ) : x ^ (i + k * d) = x ^ i := by
    induction k with
    | zero => simp
    | succ k ih =>
      calc
        x ^ (i + (k + 1) * d) = x ^ ((i + d) + k * d) := by congr 1; ring
        _ = x ^ (i + d) * x ^ (k * d) := pow_add _ _ _
        _ = x ^ i * x ^ (k * d) := by rw [hstep]
        _ = x ^ (i + k * d) := (pow_add _ _ _).symm
        _ = x ^ i := ih
  let n := (i + 1) * d
  have hn : 0 < n := Nat.mul_pos (by omega) hd
  have hin : i ≤ n := by
    have h := Nat.mul_le_mul_left (i + 1) (show 1 ≤ d from hd)
    dsimp [n]
    omega
  have hperiod := congrArg (fun y : M => y * x ^ (n - i)) (hiter (i + 1))
  change x ^ (i + n) * x ^ (n - i) = x ^ i * x ^ (n - i) at hperiod
  simp only [← pow_add] at hperiod
  have hleft : i + n + (n - i) = n + n := by omega
  have hright : i + (n - i) = n := by omega
  rw [hleft, hright] at hperiod
  exact ⟨n, hn, by simpa only [IsIdempotentElem, pow_add] using hperiod⟩

/-- Every element of a finite monoid has a positive idempotent power. -/
theorem exists_positive_idempotent_pow {M : Type*} [Monoid M] [Finite M] (x : M) :
    ∃ n : ℕ, 0 < n ∧ IsIdempotentElem (x ^ n) := by
  obtain ⟨i, j, hne, hpow⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => x ^ n)
  rcases lt_or_gt_of_ne hne with hij | hji
  · exact exists_positive_idempotent_pow_of_eq x hij hpow
  · exact exists_positive_idempotent_pow_of_eq x hji hpow.symm

/-- Correct a preimage of a unit to a unit without changing its image. -/
theorem finite_ring_unit_preimage {R S : Type*} [CommRing R] [CommRing S] [Finite R]
    (f : R →+* S) (x : R) (hx : IsUnit (f x)) :
    ∃ u : Rˣ, f (u : R) = f x := by
  obtain ⟨n, hn, he⟩ := exists_positive_idempotent_pow x
  let e := x ^ n
  let z := x ^ (n - 1)
  have hee : e * e = e := he
  have hxz : x * z = e := by
    dsimp [z, e]
    rw [← pow_succ']
    congr 1
    omega
  have hfe : f e = 1 := by
    apply (IsIdempotentElem.iff_eq_one_of_isUnit (by
      dsimp [e]
      rw [map_pow]
      exact hx.pow n)).mp
    change f e * f e = f e
    rw [← map_mul, hee]
  have hmul : (x * e + 1 - e) * (z * e + 1 - e) = 1 := by
    calc
      _ = (x * z) * (e * e) + (x + z) * (e - e * e) + (1 - e) * (1 - e) := by ring
      _ = (x * z) * e + (1 - e) * (1 - e) := by rw [hee]; ring
      _ = e + (1 - e) * (1 - e) := by rw [hxz, hee]
      _ = 1 := by linear_combination hee
  let u : Rˣ :=
    { val := x * e + 1 - e
      inv := z * e + 1 - e
      val_inv := hmul
      inv_val := by simpa only [mul_comm] using hmul }
  refine ⟨u, ?_⟩
  change f (x * e + 1 - e) = f x
  simp only [map_sub, map_add, map_mul, map_one, hfe, mul_one, add_sub_cancel_right]

/-- A surjective map from a finite commutative ring is surjective on units. -/
theorem units_map_surjective_of_finite {R S : Type*} [CommRing R] [CommRing S] [Finite R]
    (f : R →+* S) (hf : Function.Surjective f) :
    Function.Surjective (Units.map f.toMonoidHom) := by
  intro y
  obtain ⟨x, hx⟩ := hf (y : S)
  obtain ⟨u, hu⟩ := finite_ring_unit_preimage f x (hx ▸ y.isUnit)
  refine ⟨u, Units.ext ?_⟩
  exact hu.trans hx

end ArtinMatthews
