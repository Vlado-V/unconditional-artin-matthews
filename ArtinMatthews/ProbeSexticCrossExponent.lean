module

public import Mathlib.Tactic


set_option backward.privateInPublic true
@[expose] public section

/-! Exact exponents in the source05 cross-prime cancellation. These are
algebraic identities; the arithmetic equality of opposite residue symbols
is a separate input proved from reciprocity. -/
namespace ArtinMatthews.VaryingKummerAnalytic

open scoped BigOperators Classical

 theorem probeCrossStoreExponent (t t' k k' : ℤ) :
    t * k' + t' * k + (t - k) * t' + (t' - k') * t = 2 * t * t' := by ring

 theorem probeCrossTotalExponent (e l e' l' : ℤ) :
    2 * (e + 3 * l) * (e' + 3 * l') + 4 * e * e' =
      6 * (e * e' + e * l' + l * e' + 3 * l * l') := by ring

 theorem probeCrossTotalExponent_nat (e l e' l' : ℕ) :
    2 * (e + 3 * l) * (e' + 3 * l') + 4 * e * e' =
      6 * (e * e' + e * l' + l * e' + 3 * l * l') := by ring

 theorem probeCrossPair_pow_eq_one {G : Type*} [Monoid G] (z : G) (hz : z ^ 6 = 1)
    (e l e' l' : ℕ) :
    z ^ (2 * (e + 3 * l) * (e' + 3 * l')) * z ^ (4 * e * e') = 1 := by
  rw [← pow_add, probeCrossTotalExponent_nat, pow_mul, hz, one_pow]

 theorem probeCrossPair_zpow_eq_one {G : Type*} [Group G] (z : G) (hz : z ^ 6 = 1)
    (e l e' l' : ℤ) :
    z ^ (2 * (e + 3 * l) * (e' + 3 * l')) * z ^ (4 * e * e') = 1 := by
  rw [← zpow_add, probeCrossTotalExponent, zpow_mul]
  have hz' : z ^ (6 : ℤ) = 1 := by exact_mod_cast hz
  rw [hz', one_zpow]

 theorem probeCrossFinitePairs_eq_one {ι G : Type*} [CommMonoid G] (S : Finset (ι × ι))
    (z : ι → ι → G) (hz : ∀ p ∈ S, z p.1 p.2 ^ 6 = 1) (e l : ι → ℕ) :
    (∏ p ∈ S, z p.1 p.2 ^ (2 * (e p.1 + 3 * l p.1) * (e p.2 + 3 * l p.2)) *
      z p.1 p.2 ^ (4 * e p.1 * e p.2)) = 1 := by
  apply Finset.prod_eq_one
  intro p hp
  exact probeCrossPair_pow_eq_one _ (hz p hp) _ _ _ _

end ArtinMatthews.VaryingKummerAnalytic
