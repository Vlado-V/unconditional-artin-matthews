module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic.Ring.RingNF


set_option backward.privateInPublic true
@[expose] public section

/-! Exact algebra for a finite pair of omitted-prime products. No
reciprocity or cancellation premise is used in these identities. -/
namespace ArtinMatthews.SourceEulerAssembly
open scoped BigOperators
variable {I G : Type*} [CommGroup G]

theorem sourceDirectedRow_powers (S : Finset I) (z : I → G) (k t : I → ℕ) (i : I) :
    (∏ j ∈ S, z j ^ k j) ^ t i * (∏ j ∈ S, z j ^ t j) ^ ((t i : ℤ) - k i) =
      ∏ j ∈ S, z j ^ ((t i : ℤ) * k j + ((t i : ℤ) - k i) * t j) := by
  rw [← Finset.prod_pow, ← Finset.prod_zpow, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  have hk : (z j ^ k j) ^ t i = z j ^ ((t i : ℤ) * k j) := by
    rw [← pow_mul, mul_comm (k j) (t i), ← Int.natCast_mul, zpow_natCast]
  have ht : (z j ^ t j) ^ ((t i : ℤ) - k i) = z j ^ (((t i : ℤ) - k i) * t j) := by
    rw [← zpow_natCast (z j) (t j), ← zpow_mul, mul_comm (t j : ℤ)]
  rw [hk, ht, ← zpow_add]

theorem sourceDirectedPair_with_gauss (z : G) (e e' k k' t t' : ℕ) :
    z ^ (2 * e * e') * z ^ ((t : ℤ) * k' + ((t : ℤ) - k) * t') =
      z ^ ((t : ℤ) * k' + ((t : ℤ) - k) * t' + 2 * (e : ℤ) * e') := by
  rw [← zpow_natCast z (2 * e * e'), ← zpow_add]
  congr 1
  push_cast
  ring

theorem sourceDirectedProduct_with_gauss (S : Finset I) (z : I → I → G)
    (θ : I → G) (e k t : I → ℕ) :
    (∏ i ∈ S, ∏ j ∈ S, z i j ^ (2 * e i * e j)) *
      (∏ i ∈ S, θ i ^ ((k i : ℤ) - t i) *
        ∏ j ∈ S, z i j ^ ((t i : ℤ) * k j + ((t i : ℤ) - k i) * t j)) =
      (∏ i ∈ S, θ i ^ ((k i : ℤ) - t i)) *
        ∏ i ∈ S, ∏ j ∈ S,
          z i j ^ ((t i : ℤ) * k j + ((t i : ℤ) - k i) * t j + 2 * (e i : ℤ) * e j) := by
  rw [Finset.prod_mul_distrib]
  calc
    _ = (∏ i ∈ S, θ i ^ ((k i : ℤ) - t i)) *
        ((∏ i ∈ S, ∏ j ∈ S, z i j ^ (2 * e i * e j)) *
          (∏ i ∈ S, ∏ j ∈ S, z i j ^ ((t i : ℤ) * k j + ((t i : ℤ) - k i) * t j))) := by ac_rfl
    _ = (∏ i ∈ S, θ i ^ ((k i : ℤ) - t i)) *
        ∏ i ∈ S, ((∏ j ∈ S, z i j ^ (2 * e i * e j)) *
          (∏ j ∈ S, z i j ^ ((t i : ℤ) * k j + ((t i : ℤ) - k i) * t j))) := by
      rw [Finset.prod_mul_distrib]
    _ = _ := by
      congr 1
      apply Finset.prod_congr rfl
      intro i _
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro j _
      exact sourceDirectedPair_with_gauss (z i j) (e i) (e j) (k i) (k j) (t i) (t j)

end ArtinMatthews.SourceEulerAssembly
