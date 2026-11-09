module

public import ArtinMatthews.GiantSlotCutoffCore
public import ArtinMatthews.PrimeExtractionRelevantGeometry


set_option backward.privateInPublic true
@[expose] public section

/-! The original unshifted support selects the actual dyadic rectangles.
The threshold on the selected slot shortens its literal closed interval. -/

namespace ArtinMatthews
noncomputable section
open Finset
open scoped BigOperators

theorem giant_slot_cutoff_eq_relevant_dyads (A : ℕ → ℕ → ℂ) (Φ : ℝ → ℝ)
    {a T x γ : ℝ} (hx : 0 < x) (hsupp : Function.support Φ ⊆ Set.Icc a T)
    (hA : ∀ m n,A m n ≠ 0 → x^γ < (m:ℝ) ∧ x^γ < (n:ℝ)) :
    let X := ⌊T*x⌋₊
    giantSlotCutoffSum X A (fun n => (Φ ((n:ℝ)/x):ℂ)) =
      ∑ kl ∈ primeExtractionRelevantBoxes X a γ x,
        ∑ m ∈ primeExtractionDyadicBlock X kl.1,
          ∑ n ∈ primeExtractionDyadicBlock X kl.2, A m n*(Φ (((m*n:ℕ):ℝ)/x):ℂ) := by
  let X := ⌊T*x⌋₊
  let f (m n : ℕ) := A m n*(Φ (((m*n:ℕ):ℝ)/x):ℂ)
  change giantSlotCutoffSum X A (fun n => (Φ ((n:ℝ)/x):ℂ)) =
    ∑ kl ∈ primeExtractionRelevantBoxes X a γ x,
      ∑ m ∈ primeExtractionDyadicBlock X kl.1,∑ n ∈ primeExtractionDyadicBlock X kl.2,f m n
  have hz (m n : ℕ) (h : X < m*n) : f m n=0 := by
    dsimp only [f]
    rw [prime_extraction_cutoff_zero_of_product_gt Φ hsupp hx h,Complex.ofReal_zero,mul_zero]
  calc
    _ = ∑ mn ∈ (Ioc 0 X)×ˢ(Ioc 0 X),f mn.1 mn.2 := by
      apply sum_subset (filter_subset _ _)
      intro mn hm hn
      exact hz mn.1 mn.2 (lt_of_not_ge (fun h => hn (mem_filter.mpr ⟨hm,h⟩)))
    _ = ∑ m ∈ Ioc 0 X,∑ n ∈ Ioc 0 X,f m n := sum_product _ _ _
    _ = ∑ kl ∈ primeExtractionDyadicActive X,
        ∑ m ∈ primeExtractionDyadicBlock X kl.1,∑ n ∈ primeExtractionDyadicBlock X kl.2,f m n :=
      prime_extraction_dyadic_supported_sum X f hz
    _ = _ := by
      symm
      apply sum_subset (primeExtractionRelevantBoxes_subset _ _ _ _)
      intro kl hact hnot
      apply sum_eq_zero
      intro m hm
      apply sum_eq_zero
      intro n hn
      by_contra hne
      have hs := mul_ne_zero_iff.mp hne
      have hg := hA m n hs.1
      have hp := primeExtractionDyadicCutoff_height hx (primeExtraction_complexCutoff_support Φ hsupp)
        hm hn hs.2
      have hmhi : (m:ℝ) < 2*(2:ℝ)^kl.1 := by
        exact_mod_cast (primeExtractionDyadicBlock_bounds hm).2
      have hnhi : (n:ℝ) < 2*(2:ℝ)^kl.2 := by
        exact_mod_cast (primeExtractionDyadicBlock_bounds hn).2
      exact hnot (mem_filter.mpr ⟨hact,hp.2,by linarith [hg.1],by linarith [hg.2]⟩)

theorem giant_dyadic_block_eq_Icc (X k : ℕ) :
    primeExtractionDyadicBlock X k = Icc (2^k) (min X (2*2^k-1)) := by
  rw [primeExtractionDyadicBlock_eq_Ico]
  ext m
  simp only [mem_Ico,mem_Icc,lt_min_iff,le_min_iff,Nat.lt_succ_iff]
  have hp : 0 < 2*(2:ℕ)^k := by positivity
  omega

theorem giant_dyadic_block_threshold_eq_Icc (X k : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    (primeExtractionDyadicBlock X k).filter (fun m : ℕ => z < (m:ℝ)) =
      Icc (max (2^k) (⌊z⌋₊+1)) (min X (2*2^k-1)) := by
  ext m
  rw [mem_filter,giant_dyadic_block_eq_Icc,mem_Icc,mem_Icc,max_le_iff,← Nat.floor_lt hz]
  omega

end
end ArtinMatthews
