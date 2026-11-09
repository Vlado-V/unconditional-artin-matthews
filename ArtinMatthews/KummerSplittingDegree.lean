module

public import ArtinMatthews.KummerSplittingDegreeNorm
public import ArtinMatthews.KummerSplittingDegreeNonpowers
public import ArtinMatthews.KummerSplittingDegreeBase
public import Mathlib.Analysis.Complex.Polynomial.Basic


set_option backward.privateInPublic true
@[expose] public section

/-!
# Degree of the prime radical compositum

The algebraic input in the external primitive-roots Lemma 9.1 is obtained by
norm descent and prime-binomial irreducibility. No splitting-density estimate
or discriminant estimate is assumed or asserted here.
-/

open Polynomial

namespace ArtinMatthews

/-- Adjoining a root of the prime binomial to a degree-`q-1` extension has
relative degree `q`, once the rational radicand is not a rational `q`th power. -/
theorem prime_radical_adjoin_finrank
    (E : IntermediateField ℚ ℂ) [FiniteDimensional ℚ E]
    {q : ℕ} (hq : q.Prime) (hdegree : Module.finrank ℚ E = q - 1)
    {a : ℚ} (ha : a ≠ 0) (hnot : ∀ b : ℚ, b ^ q ≠ a)
    {α : ℂ} (hα : α ^ q = (a : ℂ)) :
    Module.finrank E (IntermediateField.adjoin E {α}) = q := by
  let f : E[X] := Polynomial.X ^ q - Polynomial.C (algebraMap ℚ E a)
  have hirr : Irreducible f :=
    prime_binomial_irreducible_over_finrank_pred hq hdegree ha hnot
  have hmonic : f.Monic := Polynomial.monic_X_pow_sub_C _ hq.ne_zero
  have hroot : Polynomial.aeval α f = 0 := by
    simp [f, hα]
  have hint : IsIntegral E α := ⟨f, hmonic, hroot⟩
  have hmin : f = minpoly E α := minpoly.eq_of_irreducible_of_monic hirr hroot hmonic
  rw [IntermediateField.adjoin.finrank hint, ← hmin]
  exact Polynomial.natDegree_X_pow_sub_C

/-- The absolute degree follows from the genuine field-extension tower. -/
theorem prime_radical_adjoin_absolute_finrank
    (E : IntermediateField ℚ ℂ) [FiniteDimensional ℚ E]
    {q : ℕ} (hq : q.Prime) (hdegree : Module.finrank ℚ E = q - 1)
    {a : ℚ} (ha : a ≠ 0) (hnot : ∀ b : ℚ, b ^ q ≠ a)
    {α : ℂ} (hα : α ^ q = (a : ℂ)) :
    Module.finrank ℚ (IntermediateField.adjoin E {α}) = q * (q - 1) := by
  rw [← Module.finrank_mul_finrank ℚ E (IntermediateField.adjoin E {α}),
    prime_radical_adjoin_finrank E hq hdegree ha hnot hα, hdegree, Nat.mul_comm]

/-- The actual complex field `ℚ(ζ_q, a^(1/q))`. -/
noncomputable def primeKummerField (q : ℕ) (a : ℤ) : IntermediateField ℚ ℂ :=
  (IntermediateField.adjoin (primeCyclotomicField q) {primeRadicalRoot q a}).restrictScalars ℚ

/-- Its defining two-generator description in the common complex overfield. -/
theorem primeKummerField_eq_adjoin (q : ℕ) (a : ℤ) :
    primeKummerField q a =
      IntermediateField.adjoin ℚ ({primeCyclotomicRoot q} ∪ {primeRadicalRoot q a}) := by
  exact IntermediateField.adjoin_adjoin_left (F := ℚ)
    (S := ({primeCyclotomicRoot q} : Set ℂ)) ({primeRadicalRoot q a} : Set ℂ)

/-- The algebraic degree statement in external Lemma 9.1, with an explicit
sufficient threshold depending only on the fixed integer base. -/
theorem finrank_primeKummerField_of_large_prime {a : ℤ}
    (ha0 : a ≠ 0) (ha1 : a ≠ 1) (ham1 : a ≠ -1)
    {q : ℕ} (hq : q.Prime) (haq : a.natAbs ≤ q) :
    Module.finrank ℚ (primeKummerField q a) = q * (q - 1) := by
  let : NeZero q := ⟨hq.ne_zero⟩
  exact prime_radical_adjoin_absolute_finrank (primeCyclotomicField q) hq
    (finrank_primeCyclotomicField hq) (by exact_mod_cast ha0)
    (rat_pow_ne_int_of_natAbs_le ha0 ha1 ham1 haq)
    (by simpa only [Rat.cast_intCast] using primeRadicalRoot_pow hq.pos a)

/-- Thus every sufficiently large prime has the required actual field degree. -/
theorem eventually_finrank_primeKummerField {a : ℤ}
    (ha0 : a ≠ 0) (ha1 : a ≠ 1) (ham1 : a ≠ -1) :
    ∀ᶠ q : ℕ in Filter.atTop, q.Prime →
      Module.finrank ℚ (primeKummerField q a) = q * (q - 1) := by
  filter_upwards [Filter.eventually_ge_atTop a.natAbs] with q hq
  exact fun hp => finrank_primeKummerField_of_large_prime ha0 ha1 ham1 hp hq

end ArtinMatthews
