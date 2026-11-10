module

public import ArtinMatthews.CubicReciprocityBridgeCoordinates
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
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


set_option backward.privateInPublic true
@[expose] public section

/-! The radicands of all actual Fourier characters have common finite support. -/

noncomputable section
open scoped BigOperators
namespace ArtinMatthews

/-- Every selected Fourier radicand divides the square of the original
product of bases: its coordinate exponents belong to `{0,1,2}`. -/
theorem cubicProductRadicand_dvd_product_square {S : Finset ℤ} (e : S → Fin 3) :
    cubicProductRadicand (fun i => (e i : ℕ)) ∣ (∏ a ∈ S, a) ^ 2 := by
  have hprod : (∏ i : S, i.val) = ∏ a ∈ S, a :=
    Finset.prod_coe_sort S (fun a : ℤ => a)
  rw [← hprod, ← Finset.prod_pow]
  apply Finset.prod_dvd_prod_of_dvd
  intro i _
  exact pow_dvd_pow i.val (by change (e i : ℕ) ≤ 2; have := (e i).isLt; omega)

/-- A prime avoiding the original bases avoids every Fourier radicand. -/
theorem cubicProductRadicand_prime_not_dvd {S : Finset ℤ} (e : S → Fin 3)
    {p : ℕ} (hp : p.Prime) (hS : ∀ a ∈ S, ¬ (p : ℤ) ∣ a) :
    ¬ (p : ℤ) ∣ cubicProductRadicand (fun i => (e i : ℕ)) := by
  intro h
  have hprod : (p : ℤ) ∣ (∏ a ∈ S, a) ^ 2 :=
    h.trans (cubicProductRadicand_dvd_product_square e)
  have hpz : Prime (p : ℤ) := Int.prime_iff_natAbs_prime.mpr (by simpa using hp)
  have hd : (p : ℤ) ∣ ∏ a ∈ S, a := hpz.dvd_of_dvd_pow hprod
  obtain ⟨a, ha, hpa⟩ := (hpz.dvd_finsetProd_iff (fun a : ℤ => a)).mp hd
  exact hS a ha hpa

end ArtinMatthews
