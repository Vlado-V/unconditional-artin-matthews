module

public import ArtinMatthews.Definitions
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic


set_option backward.privateInPublic true
@[expose] public section

/-!
# Exact signed-memory identities

These are the finite algebraic identities in PD §4.1. Opposite-order
telescoping produces the prefix and suffix ghost extensions. A second
telescoping expansion groups every term of degree at least two by its first
and last visits, producing exactly one ghost pair. No operator moment bound
or analytic determinant replacement is asserted here.
-/

namespace ArtinMatthews

section RingIdentities

variable {ι R : Type*} [LinearOrder ι] [CommRing R]

/-- Prefix ghost extension, telescoped from the last visit toward the first. -/
theorem marked_memory_prefix (s : Finset ι) (u : ι → R) (a : ι) :
    (∏ j ∈ s with j < a, (1 - u j)) =
      1 - ∑ h ∈ s with h < a, u h *
        ∏ j ∈ s with h < j ∧ j < a, (1 - u j) := by
  simpa only [Finset.filter_filter, and_comm] using
    (Finset.prod_one_sub_ordered' (s.filter (fun j => j < a)) u)

/-- Suffix ghost extension, telescoped from the first visit toward the last. -/
theorem marked_memory_suffix (s : Finset ι) (u : ι → R) (c : ι) :
    (∏ j ∈ s with c < j, (1 - u j)) =
      1 - ∑ h ∈ s with c < h, u h *
        ∏ j ∈ s with c < j ∧ j < h, (1 - u j) := by
  simpa only [Finset.filter_filter] using
    (Finset.prod_one_sub_ordered (s.filter (fun j => c < j)) u)

/-- Empty active-set identity: every term beyond the singleton baseline has
exactly two distinguished endpoints, with all internal damping retained. -/
theorem marked_memory_orphan (s : Finset ι) (u : ι → R) :
    (∏ j ∈ s, (1 - u j)) =
      1 - ∑ j ∈ s, u j +
        ∑ a ∈ s, ∑ c ∈ s with a < c, u a * u c *
          ∏ j ∈ s with a < j ∧ j < c, (1 - u j) := by
  rw [Finset.prod_one_sub_ordered']
  simp_rw [marked_memory_suffix, mul_sub, mul_one, Finset.sum_sub_distrib,
    Finset.mul_sum, ← mul_assoc]
  ring

end RingIdentities

section FiniteLines

variable {ι Λ R : Type*} [LinearOrder ι] [Fintype Λ] [DecidableEq Λ] [CommRing R]

/-- A visit hits precisely its assigned line. -/
def markedLineHit (line : ι → Λ) (j : ι) (ℓ : Λ) : R :=
  if ℓ = line j then 1 else 0

/-- Two endpoint hits force the same line, and then evaluate every internal
factor on that line. -/
theorem marked_line_pair_sum (a c : Λ) (ηa ηc : R) (f : Λ → R) :
    (∑ ℓ : Λ, (ηa * (if ℓ = a then 1 else 0)) *
        (ηc * (if ℓ = c then 1 else 0)) * f ℓ) =
      if a = c then ηa * ηc * f a else 0 := by
  by_cases h : a = c
  · subst c
    simp [mul_ite, ite_mul]
  · simp [mul_ite, ite_mul, h, Ne.symm h]

/-- The exact empty-active-set line sum: singletons form the baseline and
all remaining terms have exactly one pair of ghost endpoints. -/
theorem marked_memory_orphan_line_sum (s : Finset ι) (η : ι → R) (line : ι → Λ) :
    (∑ ℓ : Λ, ∏ j ∈ s, (1 - η j * markedLineHit line j ℓ)) =
      (Fintype.card Λ : R) - ∑ j ∈ s, η j +
        ∑ a ∈ s, ∑ c ∈ s with a < c,
          if line a = line c then η a * η c *
            ∏ j ∈ s with a < j ∧ j < c, (1 - η j * markedLineHit line j (line a))
          else 0 := by
  classical
  have hsingle : (∑ ℓ : Λ, ∑ j ∈ s, η j * markedLineHit line j ℓ) =
      ∑ j ∈ s, η j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _hj
    simp [markedLineHit, mul_ite]
  have hpair : (∑ ℓ : Λ, ∑ a ∈ s, ∑ c ∈ s with a < c,
        (η a * markedLineHit line a ℓ) * (η c * markedLineHit line c ℓ) *
          ∏ j ∈ s with a < j ∧ j < c, (1 - η j * markedLineHit line j ℓ)) =
      ∑ a ∈ s, ∑ c ∈ s with a < c,
        if line a = line c then η a * η c *
          ∏ j ∈ s with a < j ∧ j < c, (1 - η j * markedLineHit line j (line a))
        else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _ha
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro c _hc
    exact marked_line_pair_sum (line a) (line c) (η a) (η c) _
  have horphan : (∑ ℓ : Λ, ∏ j ∈ s, (1 - η j * markedLineHit line j ℓ)) =
      ∑ ℓ : Λ, (1 - ∑ j ∈ s, η j * markedLineHit line j ℓ +
        ∑ a ∈ s, ∑ c ∈ s with a < c,
          (η a * markedLineHit line a ℓ) * (η c * markedLineHit line c ℓ) *
            ∏ j ∈ s with a < j ∧ j < c, (1 - η j * markedLineHit line j ℓ)) := by
    apply Finset.sum_congr rfl
    intro ℓ _hℓ
    exact marked_memory_orphan s (fun j => η j * markedLineHit line j ℓ)
  rw [horphan]
  simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hsingle, hpair]
  simp

end FiniteLines

/-- Uniform line averaging yields the exact orphan identity with its
singleton baseline. This is PD's primewise formula before any estimates. -/
theorem marked_memory_orphan_line_average {ι Λ : Type*} [LinearOrder ι]
    [Fintype Λ] [DecidableEq Λ] [Nonempty Λ]
    (s : Finset ι) (η : ι → ℝ) (line : ι → Λ) :
    (∑ ℓ : Λ, ∏ j ∈ s, (1 - η j * markedLineHit line j ℓ)) /
        (Fintype.card Λ : ℝ) =
      1 - (∑ j ∈ s, η j) / (Fintype.card Λ : ℝ) +
        (1 / (Fintype.card Λ : ℝ)) *
          ∑ a ∈ s, ∑ c ∈ s with a < c,
            if line a = line c then η a * η c *
              ∏ j ∈ s with a < j ∧ j < c,
                (1 - η j * markedLineHit line j (line a))
            else 0 := by
  rw [marked_memory_orphan_line_sum]
  have hn : (Fintype.card Λ : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp [hn]


end ArtinMatthews
