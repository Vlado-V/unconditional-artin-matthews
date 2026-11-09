module

public import ArtinMatthews.ShiftedConvolutionCoefficients


set_option backward.privateInPublic true
@[expose] public section

/-! The true zero dual-frequency fiber has injective coordinate projections.
Its absolute coefficient sum is controlled without a multiplicity factor. -/

noncomputable section
open scoped BigOperators
namespace ArtinMatthews

def shiftedDualZeroPairs (S T : Finset ℕ) (m3 m4 : ℕ) : Finset (ℕ × ℕ) :=
  (S ×ˢ T).filter (fun k => m4 * k.2 = m3 * k.1)

theorem shiftedDualZeroPairs_fst_injective (S T : Finset ℕ) (m3 m4 : ℕ)
    (hm4 : 0 < m4) : Set.InjOn (fun k : ℕ × ℕ => k.1) (↑(shiftedDualZeroPairs S T m3 m4) : Set (ℕ × ℕ)) := by
  intro x hx y hy hxy
  have hx' := (Finset.mem_filter.mp hx).2
  have hy' := (Finset.mem_filter.mp hy).2
  have h2 : x.2 = y.2 := Nat.eq_of_mul_eq_mul_left hm4
    (hx'.trans ((congrArg (fun n => m3 * n) hxy).trans hy'.symm))
  exact Prod.ext hxy h2

theorem shiftedDualZeroPairs_snd_injective (S T : Finset ℕ) (m3 m4 : ℕ)
    (hm3 : 0 < m3) : Set.InjOn (fun k : ℕ × ℕ => k.2) (↑(shiftedDualZeroPairs S T m3 m4) : Set (ℕ × ℕ)) := by
  intro x hx y hy hxy
  have hx' := (Finset.mem_filter.mp hx).2
  have hy' := (Finset.mem_filter.mp hy).2
  have h1 : x.1 = y.1 := Nat.eq_of_mul_eq_mul_left hm3
    (hx'.symm.trans ((congrArg (fun n => m4 * n) hxy).trans hy'))
  exact Prod.ext h1 hxy

theorem shiftedDualZero_energy_bound (S T : Finset ℕ) (m3 m4 : ℕ)
    (hm3 : 0 < m3) (hm4 : 0 < m4) (a b : ℕ → ℂ) :
    (∑ k ∈ shiftedDualZeroPairs S T m3 m4, ‖a k.1 * b k.2‖)^2 ≤
      (∑ k ∈ S, ‖a k‖^2) * (∑ k ∈ T, ‖b k‖^2) := by
  classical
  let P := shiftedDualZeroPairs S T m3 m4
  have hfirst : (∑ k ∈ P, ‖a k.1‖^2) ≤ ∑ k ∈ S, ‖a k‖^2 := by
    dsimp only [P]
    rw [← Finset.sum_image (f := fun k : ℕ => ‖a k‖^2) (shiftedDualZeroPairs_fst_injective S T m3 m4 hm4)]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · rintro k hk
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hk
      exact (Finset.mem_product.mp (Finset.mem_filter.mp hx).1).1
    · intro k _ _
      exact sq_nonneg _
  have hsecond : (∑ k ∈ P, ‖b k.2‖^2) ≤ ∑ k ∈ T, ‖b k‖^2 := by
    dsimp only [P]
    rw [← Finset.sum_image (f := fun k : ℕ => ‖b k‖^2) (shiftedDualZeroPairs_snd_injective S T m3 m4 hm3)]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · rintro k hk
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hk
      exact (Finset.mem_product.mp (Finset.mem_filter.mp hx).1).2
    · intro k _ _
      exact sq_nonneg _
  simp_rw [norm_mul]
  exact (Finset.sum_mul_sq_le_sq_mul_sq P (fun k => ‖a k.1‖) (fun k => ‖b k.2‖)).trans
    (mul_le_mul hfirst hsecond (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      (Finset.sum_nonneg fun _ _ => sq_nonneg _))

end ArtinMatthews
