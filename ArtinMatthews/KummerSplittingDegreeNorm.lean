module

public import Mathlib.FieldTheory.KummerExtension
public import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots


set_option backward.privateInPublic true
@[expose] public section

/-!
# Norm descent for prime radical degrees

A `q`th root of an element in an extension of degree `q-1` would give a
`q`th root in the ground field by taking norms. This avoids any ramification
assumption in the degree computation.
-/

namespace ArtinMatthews

/-- Norm descent in an extension of degree one less than the exponent. -/
theorem no_power_in_extension_of_finrank_pred
    {F E : Type*} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    {q : ℕ} (hq : 0 < q) (hdegree : Module.finrank F E = q - 1)
    {a : F} (ha : a ≠ 0) (hnot : ∀ b : F, b ^ q ≠ a) :
    ∀ b : E, b ^ q ≠ algebraMap F E a := by
  intro b hb
  have hnorm : (Algebra.norm F b) ^ q = a ^ (q - 1) := by
    have h := congrArg (Algebra.norm F) hb
    simpa only [map_pow, Algebra.norm_algebraMap, hdegree] using h
  have haeq : a ^ q = a ^ (q - 1) * a := by
    rw [← pow_succ, Nat.sub_add_cancel hq]
  apply hnot (a / Algebra.norm F b)
  rw [div_pow, hnorm, haeq]
  exact mul_div_cancel_left₀ _ (pow_ne_zero _ ha)

/-- In a degree-`q-1` extension the binomial remains irreducible whenever it
is a prime-degree binomial without a root over the base field. -/
theorem prime_binomial_irreducible_over_finrank_pred
    {F E : Type*} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    {q : ℕ} (hq : q.Prime) (hdegree : Module.finrank F E = q - 1)
    {a : F} (ha : a ≠ 0) (hnot : ∀ b : F, b ^ q ≠ a) :
    Irreducible (Polynomial.X ^ q - Polynomial.C (algebraMap F E a)) :=
  X_pow_sub_C_irreducible_of_prime hq
    (no_power_in_extension_of_finrank_pred hq.pos hdegree ha hnot)

end ArtinMatthews
