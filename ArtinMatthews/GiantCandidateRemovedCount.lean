module

public import ArtinMatthews.GiantCandidateRemovedLog
public import ArtinMatthews.PrimeExtractionDyadicPartition


set_option backward.privateInPublic true
@[expose] public section

/-! Large removals on a dyadic integer interval are counted before
imposing roughness. -/

namespace ArtinMatthews
noncomputable section
open Finset
open scoped BigOperators

theorem giantCandidateRemovedLog_count_mul_le (P : Finset ℕ) (R : ℝ) (N : ℕ) :
    (((Ioc 0 N).filter (fun m => R < giantCandidateRemovedLog P m)).card:ℝ)*R ≤
      ∑ m ∈ Ioc 0 N,giantCandidateRemovedLog P m := by
  let B := (Ioc 0 N).filter (fun m => R < giantCandidateRemovedLog P m)
  change (B.card:ℝ)*R ≤ _
  calc
    _ = ∑ _m ∈ B,R := by rw [sum_const,nsmul_eq_mul]
    _ ≤ ∑ m ∈ B,giantCandidateRemovedLog P m :=
      sum_le_sum (fun _ hm => (mem_filter.mp hm).2.le)
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      (fun m _ _ => giantCandidateRemovedLog_nonneg P m)

theorem giantCandidateLargeRemovalDyad_card_le {L : ℝ} (hL : 0 < L) (P : Finset ℕ)
    (hP : ∀ p ∈ P,p.Prime)
    (hPtop : ∀ p ∈ P,(p:ℝ) ≤ Real.exp (L^(9/20:ℝ)))
    (N k : ℕ) :
    (((primeExtractionDyadicBlock N k).filter
      (fun m => L^(9/10:ℝ) < giantCandidateRemovedLog P m)).card:ℝ) ≤
        8*(2:ℝ)^k*L^(-(9/20:ℝ)) := by
  let R := L^(9/10:ℝ)
  let M : ℕ := 2*2^k
  let B := (primeExtractionDyadicBlock N k).filter (fun m => R < giantCandidateRemovedLog P m)
  let C := (Ioc 0 M).filter (fun m => R < giantCandidateRemovedLog P m)
  have hsub : B ⊆ C := by
    intro m hm
    obtain ⟨hb,hr⟩ := mem_filter.mp hm
    exact mem_filter.mpr ⟨mem_Ioc.mpr
      ⟨(mem_Ioc.mp (mem_filter.mp hb).1).1,(primeExtractionDyadicBlock_bounds hb).2.le⟩,hr⟩
  have hR : 0 < R := Real.rpow_pos_of_pos hL _
  change (B.card:ℝ) ≤ _
  calc
    _ ≤ (C.card:ℝ) := Nat.cast_le.mpr (card_le_card hsub)
    _ ≤ (4*(M:ℝ)*L^(9/20:ℝ))/R := (le_div_iff₀ hR).mpr
      ((giantCandidateRemovedLog_count_mul_le P R M).trans
        (giant_candidate_removed_log_actual_bound hL.le P hP hPtop M))
    _ = _ := by
      rw [mul_div_assoc]
      change 4*(M:ℝ)*(L^(9/20:ℝ)/L^(9/10:ℝ)) = _
      rw [← Real.rpow_sub hL]
      rw [show (9/20:ℝ)-9/10=-(9/20) by norm_num]
      simp only [M,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
      ring

end
end ArtinMatthews
