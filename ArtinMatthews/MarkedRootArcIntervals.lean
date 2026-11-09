module

public import ArtinMatthews.MarkedRootArcMajorant


set_option backward.privateInPublic true
@[expose] public section

/-! Explicit finite interval covers for every elementary root arc on
the canonical root range [0,1]. Each frequency n uses only n+3 intervals. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def markedRootArcWindow (n : ℕ) : Finset ℤ := Finset.Icc (-1) ((n:ℤ)+1)

def markedRootArcInterval (n : ℕ) (ε : ℝ) (k : ℤ) : Set ℝ :=
  Set.Icc (((k:ℝ)-ε)/n) (((k:ℝ)+ε)/n)

theorem markedRootArcInterval_iff {n : ℕ} (hn : 0 < n) (ε r : ℝ) (k : ℤ) :
    r ∈ markedRootArcInterval n ε k ↔ |(n:ℝ)*r-k| ≤ ε := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  simp only [markedRootArcInterval,Set.mem_Icc,div_le_iff₀ hnR,le_div_iff₀ hnR,abs_le]
  constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> nlinarith

theorem markedBadRootMultiple_nat_interval_cover
    {n : ℕ} (hn : 0 < n) {ε r : ℝ} (hε : ε ≤ 1) (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1) :
    (r:AddCircle (1:ℝ)) ∈ markedBadRootMultiple n ε ↔
      ∃ k ∈ markedRootArcWindow n,r ∈ markedRootArcInterval n ε k := by
  have hnorm : ‖(n:ℤ) • (r:AddCircle (1:ℝ))‖ = |(n:ℝ)*r-round ((n:ℝ)*r)| := by
    have he : (n:ℤ) • (r:AddCircle (1:ℝ)) = (((n:ℝ)*r:ℝ):AddCircle (1:ℝ)) := by
      calc
        _ = (((n:ℤ) • r:ℝ):AddCircle (1:ℝ)) :=
          (AddCircle.coe_zsmul (1:ℝ) (n := (n:ℤ)) (x := r)).symm
        _ = _ := by congr 1; simp only [zsmul_eq_mul,Int.cast_natCast]
    rw [he]
    simpa only [inv_one,one_mul,mul_one] using
      (AddCircle.norm_eq (p := (1:ℝ)) (x := (n:ℝ)*r))
  change ‖(n:ℤ) • (r:AddCircle (1:ℝ))‖ ≤ ε ↔ _
  rw [hnorm]
  constructor
  · intro h
    refine ⟨round ((n:ℝ)*r),?_,(markedRootArcInterval_iff hn ε r _).mpr h⟩
    have hp₀ : 0 ≤ (n:ℝ)*r := mul_nonneg (Nat.cast_nonneg _) hr₀
    have hp₁ : (n:ℝ)*r ≤ n := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have hh := abs_le.mp h
    have hlo : (-1:ℝ) ≤ (round ((n:ℝ)*r):ℝ) := by linarith
    have hhi : (round ((n:ℝ)*r):ℝ) ≤ (n:ℝ)+1 := by linarith
    apply Finset.mem_Icc.mpr
    constructor
    · exact_mod_cast hlo
    · exact_mod_cast hhi
  · rintro ⟨k,_,hk⟩
    exact (round_le ((n:ℝ)*r) k).trans ((markedRootArcInterval_iff hn ε r k).mp hk)

theorem markedBadRootMultiple_natAbs (q : ℤ) (ε : ℝ) :
    markedBadRootMultiple q ε = markedBadRootMultiple (q.natAbs:ℤ) ε := by
  ext θ
  change ‖q • θ‖ ≤ ε ↔ ‖(q.natAbs:ℤ) • θ‖ ≤ ε
  rw [Int.natCast_natAbs]
  by_cases hq : 0 ≤ q
  · rw [abs_of_nonneg hq]
  · rw [abs_of_neg (lt_of_not_ge hq),neg_smul,norm_neg]

theorem markedRootArcWindow_card (n : ℕ) : (markedRootArcWindow n).card = n+3 := by
  simp [markedRootArcWindow,Int.card_Icc]
  omega

theorem markedBadRootMultiple_interval_majorant (q : ℤ) (hq : q ≠ 0)
    {ε r : ℝ} (hε : ε ≤ 1) (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1) :
    (if (r:AddCircle (1:ℝ)) ∈ markedBadRootMultiple q ε then (1:ℝ) else 0) ≤
      ∑ k ∈ markedRootArcWindow q.natAbs,if r ∈ markedRootArcInterval q.natAbs ε k then (1:ℝ) else 0 := by
  rw [markedBadRootMultiple_natAbs]
  by_cases h : (r:AddCircle (1:ℝ)) ∈ markedBadRootMultiple (q.natAbs:ℤ) ε
  · obtain ⟨k,hk,hr⟩ := (markedBadRootMultiple_nat_interval_cover (Int.natAbs_pos.mpr hq) hε hr₀ hr₁).mp h
    rw [ite_eq_left h]
    have hs := Finset.single_le_sum (s := markedRootArcWindow q.natAbs)
      (f := fun k => if r ∈ markedRootArcInterval q.natAbs ε k then (1:ℝ) else 0)
      (fun k _ => by split_ifs <;> norm_num) hk
    simpa only [ite_eq_left hr] using hs
  · rw [ite_eq_right h]
    exact Finset.sum_nonneg (fun k _ => by split_ifs <;> norm_num)

end
end ArtinMatthews
