module

public import ArtinMatthews.SpectralPositiveModulusReindex
public import Mathlib.Analysis.PSeries


set_option backward.privateInPublic true
@[expose] public section

/-! Actual summation of a power bound on finitely supported positive
moduli divisible by a level. The divisibility is used by an injective
reindexing, retaining the full factor N^p. -/

noncomputable section
open Set
open scoped BigOperators

namespace ArtinMatthews

theorem spectral_positive_multiple_finsum_norm_bound (N : ℕ)
    (F : Ioi (0 : ℕ) → ℂ) (hF : Function.HasFiniteSupport F)
    (hzero : ∀ c : Ioi (0 : ℕ), ¬ N ∣ c.val → F c = 0)
    {p A : ℝ} (hp : p < -1) (hA : 0 ≤ A)
    (hb : ∀ c : Ioi (0 : ℕ), ‖F c‖ ≤ A*(c.val : ℝ)^p) :
    ‖∑ᶠ c : Ioi (0 : ℕ), F c‖ ≤
      A*(N : ℝ)^p*(∑' k : ℕ, ((k+1 : ℕ) : ℝ)^p) := by
  classical
  let S := hF.toFinset
  let j (c : Ioi (0 : ℕ)) := c.val/N-1
  have hdiv (c : Ioi (0 : ℕ)) (hc : c ∈ S) : N ∣ c.val := by
    by_contra hNc
    exact (hF.mem_toFinset.mp hc) (hzero c hNc)
  have hRep (c : Ioi (0 : ℕ)) (hc : c ∈ S) : c.val = N*(j c+1) := by
    have he := Nat.div_mul_cancel (hdiv c hc)
    have hpos : 0 < c.val := c.property
    have h1 : 1 ≤ c.val/N := by
      by_contra h
      have hz : c.val/N = 0 := Nat.eq_zero_of_not_pos
        (fun hpos' : 0 < c.val/N => h (Nat.succ_le_iff.mpr hpos'))
      rw [hz,zero_mul] at he
      exact hpos.ne' he.symm
    have hj : j c+1 = c.val/N := Nat.sub_add_cancel h1
    calc
      _ = (c.val/N)*N := he.symm
      _ = _ := by rw [hj,mul_comm]
  have hj : Set.InjOn j (S : Set (Ioi (0 : ℕ))) := by
    intro c hc d hd h
    apply Subtype.ext
    rw [hRep c hc,hRep d hd,h]
  have hs : Summable (fun k : ℕ => ((k+1 : ℕ) : ℝ)^p) :=
    (Real.summable_nat_rpow.mpr hp).comp_injective Nat.succ_injective
  rw [finsum_eq_sum F hF]
  change ‖∑ c ∈ S, F c‖ ≤ _
  calc
    _ ≤ ∑ c ∈ S, ‖F c‖ := norm_sum_le _ _
    _ ≤ ∑ c ∈ S, A*(N : ℝ)^p*((j c+1 : ℕ) : ℝ)^p := by
      apply Finset.sum_le_sum
      intro c hc
      have h := hb c
      have he : (c.val : ℝ) = (N : ℝ)*((j c+1 : ℕ) : ℝ) := by exact_mod_cast hRep c hc
      rw [he,Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)] at h
      simpa only [mul_assoc] using h
    _ = A*(N : ℝ)^p*(∑ c ∈ S, ((j c+1 : ℕ) : ℝ)^p) := by rw [Finset.mul_sum]
    _ = A*(N : ℝ)^p*(∑ k ∈ S.image j, ((k+1 : ℕ) : ℝ)^p) := by rw [Finset.sum_image hj]
    _ ≤ _ := mul_le_mul_of_nonneg_left (hs.sum_le_tsum _ (fun _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (mul_nonneg hA (Real.rpow_nonneg (Nat.cast_nonneg _) _))

end ArtinMatthews
