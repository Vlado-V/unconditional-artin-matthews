module

public import ArtinMatthews.GiantTwoSidedRootMargin
public import ArtinMatthews.PrimeExtractionDyadicPartition


set_option backward.privateInPublic true
@[expose] public section

/-! A finite collection of physical edges is partitioned by its source
position into the literal root intervals used in the moment bound. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section

theorem giantTwoSidedRootInterval_nat_dyadic (k : ℕ) :
    giantTwoSidedRootInterval ((2 ^ k : ℕ) : ℝ) = Ico (2 ^ k) (2 * 2 ^ k) := by
  unfold giantTwoSidedRootInterval
  rw [show (2 : ℝ) * ((2 ^ k : ℕ) : ℝ) = ((2 * 2 ^ k : ℕ) : ℝ) by push_cast; rfl]
  simp only [Nat.ceil_natCast]

theorem giantPhysicalDyadic_partition {ι R : Type*} [AddCommMonoid R]
    (edges : Finset ι) (position : ι → ℕ) (A : ι → R) (N : ℕ)
    (hpos : ∀ e ∈ edges, 0 < position e) (hcap : ∀ e ∈ edges, position e ≤ N) :
    (∑ e ∈ edges, A e) = ∑ k ∈ range (Nat.log 2 N + 1),
      ∑ e ∈ edges.filter (fun e => position e ∈ giantTwoSidedRootInterval ((2 ^ k : ℕ) : ℝ)), A e := by
  classical
  have he (k : ℕ) : edges.filter (fun e => Nat.log 2 (position e) = k) =
      edges.filter (fun e => position e ∈ giantTwoSidedRootInterval ((2 ^ k : ℕ) : ℝ)) := by
    apply filter_congr
    intro e he
    rw [giantTwoSidedRootInterval_nat_dyadic]
    constructor
    · intro hlog
      exact mem_Ico.mpr ⟨by simpa only [hlog] using Nat.pow_log_le_self 2 (hpos e he).ne',
        by simpa only [hlog, pow_succ'] using Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (position e)⟩
    · intro h
      exact Nat.log_eq_of_pow_le_of_lt_pow (mem_Ico.mp h).1
        (by simpa only [pow_succ'] using (mem_Ico.mp h).2)
  simp_rw [← he]
  symm
  exact sum_fiberwise_of_maps_to (fun e he => mem_range.mpr
    (Nat.lt_succ_of_le (Nat.log_mono_right (hcap e he)))) A

theorem giantPhysicalDyadic_norm_le {ι : Type*}
    (edges : Finset ι) (position : ι → ℕ) (A : ι → ℂ) (N : ℕ)
    (hpos : ∀ e ∈ edges, 0 < position e) (hcap : ∀ e ∈ edges, position e ≤ N)
    {B : ℝ} (hB : 0 ≤ B)
    (hblock : ∀ k ∈ range (Nat.log 2 N + 1),
      ‖∑ e ∈ edges.filter (fun e => position e ∈ giantTwoSidedRootInterval ((2 ^ k : ℕ) : ℝ)), A e‖ ≤ B) :
    ‖∑ e ∈ edges, A e‖ ≤ (1 + Real.log (N + 1) / Real.log 2) * B := by
  rw [giantPhysicalDyadic_partition edges position A N hpos hcap]
  calc
    _ ≤ ∑ k ∈ range (Nat.log 2 N + 1),
        ‖∑ e ∈ edges.filter (fun e => position e ∈ giantTwoSidedRootInterval ((2 ^ k : ℕ) : ℝ)), A e‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _k ∈ range (Nat.log 2 N + 1), B := sum_le_sum hblock
    _ = ((Nat.log 2 N + 1 : ℕ) : ℝ) * B := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (primeExtractionDyadicIndex_count_le N) hB

end
end ArtinMatthews
