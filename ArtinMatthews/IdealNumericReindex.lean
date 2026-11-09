module

public import ArtinMatthews.IdealFiberCollapse


set_option backward.privateInPublic true
@[expose] public section

/-! Exact numerical-product reindexing of arbitrary signed tuple tests. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {Ω : Type*} [Fintype Ω]

theorem idealNumeric_sum (p : Ω → ℕ) (f : Ω → ℂ) (S : Finset ℕ)
    (hs : ∀ a, p a ∉ S → f a = 0) :
    (∑ a, f a) = ∑ n ∈ S, ∑ a, if p a = n then f a else 0 := by
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  rw [sum_ite_eq]
  by_cases ha : p a ∈ S
  · rw [ite_eq_left ha]
  · rw [ite_eq_right ha, hs a ha]

theorem idealNumeric_sum_kernel (p : Ω → ℕ) (f : Ω → ℂ) (S : Finset ℕ)
    (hs : ∀ a, p a ∉ S → f a = 0) (K : ℕ → ℂ) :
    (∑ a, f a*K (p a)) = ∑ n ∈ S, (∑ a, if p a = n then f a else 0)*K n := by
  rw [idealNumeric_sum p (fun a => f a*K (p a)) S (fun a ha => by rw [hs a ha, zero_mul])]
  apply sum_congr rfl
  intro n _
  rw [sum_mul]
  apply sum_congr rfl
  intro a _
  split_ifs with ha
  · rw [ha]
  · rw [zero_mul]

theorem idealNumeric_bilinear {Λ : Type*} [Fintype Λ]
    (p : Ω → ℕ) (q : Λ → ℕ) (f : Ω → ℂ) (g : Λ → ℂ)
    (S T : Finset ℕ) (hf : ∀ a, p a ∉ S → f a = 0) (hg : ∀ b, q b ∉ T → g b = 0)
    (K : ℕ → ℕ → ℂ) :
    (∑ a, f a * ∑ b, g b*K (p a) (q b)) =
      ∑ n ∈ S, (∑ a, if p a = n then f a else 0) *
        ∑ m ∈ T, (∑ b, if q b = m then g b else 0)*K n m := by
  calc
    _ = ∑ n ∈ S, (∑ a, if p a = n then f a else 0) * ∑ b, g b*K n (q b) :=
      idealNumeric_sum_kernel p f S hf (fun n => ∑ b, g b*K n (q b))
    _ = _ := by
      apply sum_congr rfl
      intro n _
      rw [idealNumeric_sum_kernel q g T hg (K n)]

end
end ArtinMatthews
