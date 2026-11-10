module

public import ArtinMatthews.CubicReciprocityBridgeRationalFrobenius
public import ArtinMatthews.CubicReciprocityBridgeActual
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev
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
public import OAI.NumberTheory.DirichletL.GaussSum.QuadraticTrace


set_option backward.privateInPublic true
@[expose] public section

/-! Cubic Fourier values at the original rational arithmetic Frobenius. -/

noncomputable section
open scoped NumberField
namespace ArtinMatthews
open OAI OAI.ActualEisensteinCubic
local notation "EO" => OAI.SevenEighths.HeckeFamily.O

namespace IntegralFrobeniusData
variable {S : Finset ℤ} {p : ℕ} [Fact p.Prime]
  (D : IntegralFrobeniusData (integerCubicField S) p)

omit [Fact p.Prime] in
theorem eisenstein_int_not_mem {a : ℤ} (ha : ¬ (p : ℤ) ∣ a) :
    (a : EO) ∉ D.eisensteinPrime := by
  intro h
  apply D.int_not_mem ha
  change algebraMap EO (𝓞 (integerCubicField S)) (a : EO) ∈ D.primeIdeal at h
  simpa only [map_intCast] using h

/-- The split rational progression automatically avoids the ramified
Eisenstein prime; this is derived from the actual prime above `p`. -/
theorem eisensteinPrime_good (hp3 : p % 3 = 1) : lambda ∉ D.eisensteinPrime := by
  have hpd : ¬ p ∣ 3 := by
    intro h
    rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp h with h | h
    · exact (Fact.out : p.Prime).ne_one h
    · omega
  have h3 : (3 : EO) ∉ D.eisensteinPrime :=
    D.eisenstein_int_not_mem (by exact_mod_cast hpd)
  intro hlam
  apply h3
  have heq : lambda * (omega ^ 2 - 1) = (3 : EO) := by
    change (omega - 1) * (omega ^ 2 - 1) = 3
    linear_combination (omega - 2) * omega_sq_for_norm
  rw [← heq]
  exact D.eisensteinPrime.mul_mem_right _ hlam

end IntegralFrobeniusData

/-- The genuine Fourier character equals a cubic residue symbol at every
rational split prime avoiding its explicit integer radicand. -/
theorem cubicFourier_character_has_rational_prime_symbol {S : Finset ℤ}
    (hzero : ∀ a ∈ S, a ≠ 0)
    (χ : AddChar (Additive (integerCubicGaloisGroup S)) ℂ) :
    ∃ A : ℤ, A ≠ 0 ∧
      ∀ (p : ℕ) [Fact p.Prime] (hp3 : p % 3 = 1)
        (D : IntegralFrobeniusData (integerCubicField S) p),
        ¬ (p : ℤ) ∣ A →
        χ (Additive.ofMul (relativeCubicFrobenius D hp3)) =
          @ConcreteTraceCRT.eisEmbedding
            (@cubicChar D.eisensteinPrime D.eisensteinPrime_maximal
              (D.eisensteinPrime_good hp3)
              (Ideal.Quotient.mk D.eisensteinPrime (A : EO))) := by
  obtain ⟨A, hA0, hA⟩ := cubicFourier_character_has_prime_symbol hzero χ
  refine ⟨A, hA0, ?_⟩
  intro p hp hp3 D hAp
  let : D.eisensteinPrime.IsMaximal := D.eisensteinPrime_maximal
  exact hA D.eisensteinPrime (D.toEisensteinFrobeniusData hp3)
    (D.eisensteinPrime_good hp3) (D.eisenstein_int_not_mem hAp)

end ArtinMatthews
