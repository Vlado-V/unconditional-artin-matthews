module

public import OAI.NumberTheory.PrimePackets.IdealCoefficients
public import ArtinMatthews.CubicThetaCoefficients
public import ArtinMatthews.QuadraticIdealNormCountPrimePower


set_option backward.privateInPublic true
@[expose] public section

/-! The sharp global divisor bound obtained from quadratic prime-power norm fibers. -/

noncomputable section

namespace ArtinMatthews

open OAI OAI.SevenEighths
open scoped BigOperators

/-- A multiplicative natural-valued arithmetic function bounded by `r+1`
on prime powers is bounded by the number of divisors. -/
theorem multiplicative_nat_le_divisors_card (f : ArithmeticFunction ℕ)
    (hf : f.IsMultiplicative)
    (hlocal : ∀ (p : ℕ), p.Prime → ∀ r : ℕ, f (p ^ r) ≤ r + 1)
    (n : ℕ) : f n ≤ n.divisors.card := by
  by_cases hn : n = 0
  · simp [hn]
  rw [hf.multiplicative_factorization _ hn, Nat.card_divisors hn]
  simp only [Finsupp.prod, Nat.support_factorization]
  apply Finset.prod_le_prod₀ (fun _ _ => Nat.zero_le _)
  intro p hp
  exact hlocal p (Nat.prime_of_mem_primeFactors hp) _

/-- The concrete Eisenstein integer ring has rank two. -/
theorem heckeRingOfIntegers_finrank_two :
    Module.finrank ℤ HeckeFamily.O = 2 := by
  rw [NumberField.RingOfIntegers.rank HeckeFamily.K,
    IsCyclotomicExtension.Rat.finrank 3 HeckeFamily.K]
  decide

/-- The actual finite norm fiber has the cardinality used by the multiplicative
ideal-counting arithmetic function, at nonzero indices. -/
theorem idealsOfNorm_card_eq_idealCoefficient {n : ℕ} (hn : n ≠ 0) :
    (idealsOfNorm n).card = OAI.PrimeDegreePackets.idealCoefficient HeckeFamily.K n := by
  classical
  rw [OAI.PrimeDegreePackets.idealCoefficient_pos _ _ hn]
  let e : ↥(idealsOfNorm n) ≃
      {I : Ideal HeckeFamily.O // Ideal.absNorm I = n} :=
    { toFun := fun I => ⟨I.1, mem_idealsOfNorm.mp I.2⟩
      invFun := fun I => ⟨I.1, mem_idealsOfNorm.mpr I.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  calc
    (idealsOfNorm n).card = Nat.card ↥(idealsOfNorm n) := by
      simp only [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ = Nat.card {I : Ideal HeckeFamily.O // Ideal.absNorm I = n} := Nat.card_congr e

/-- The actual ideal-counting coefficient of any quadratic number field is
bounded by the ordinary divisor function, including the zero index. -/
theorem quadraticIdealCoefficient_le_divisors_card
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℤ (NumberField.RingOfIntegers K) = 2) (n : ℕ) :
    OAI.PrimeDegreePackets.idealCoefficient K n ≤ n.divisors.card := by
  apply multiplicative_nat_le_divisors_card _
    (OAI.PrimeDegreePackets.idealCoefficient_multiplicative K)
  intro p hp r
  exact quadraticIdealCoefficient_prime_pow_le K hdegree hp r

/-- The concrete nonzero Eisenstein norm fiber has at most `τ(n)` ideals. -/
theorem idealsOfNorm_card_le_divisors_card {n : ℕ} (hn : n ≠ 0) :
    (idealsOfNorm n).card ≤ n.divisors.card := by
  rw [idealsOfNorm_card_eq_idealCoefficient hn]
  exact quadraticIdealCoefficient_le_divisors_card HeckeFamily.K
    heckeRingOfIntegers_finrank_two n

/-- Sharp divisor bound for the actual ideal-sum theta coefficients. At index
zero the ideal character vanishes on the zero ideal. -/
theorem idealThetaCoeff_norm_le_divisors_card (χ : HeckeFamily.Character) (n : ℕ) :
    ‖idealThetaCoeff χ n‖ ≤ (n.divisors.card : ℝ) := by
  by_cases hn : n = 0
  · simp [hn]
  apply (idealThetaCoeff_norm_le_card χ n).trans
  exact_mod_cast idealsOfNorm_card_le_divisors_card hn

end ArtinMatthews
