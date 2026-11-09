module

public import ArtinMatthews.IdealSourceProbeCaps


set_option backward.privateInPublic true
@[expose] public section

/-! The actual residual family has uniform fresh-label and collision counts. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem idealSourceResidual_freshCount {G : Type*} [Fintype G] [DecidableEq G]
    (S T : Finset G) {m J ell : ℕ} (hm : m ≤ J) (ν : IdealResidualPattern G J)
    (hν : ν ∈ idealResidualPatterns (idealSourceProbes S hm) (idealSourceProbes T hm)) :
    (∑ g, ((idealResidualCopied ν g).card + ell)) ≤ Fintype.card G * (m + ell) := by
  calc
    _ ≤ ∑ _g : G, (m + ell) := sum_le_sum fun g _ =>
      Nat.add_le_add_right (idealSourceResidualCopied_card_le S T hm ν hν g) ell
    _ = _ := by simp

theorem idealSourceResidual_comparisonCount {G : Type*} [Fintype G] [DecidableEq G]
    (S T : Finset G) {m J ell : ℕ} (hm : m ≤ J) (ν : IdealResidualPattern G J)
    (hν : ν ∈ idealResidualPatterns (idealSourceProbes S hm) (idealSourceProbes T hm)) :
    (∑ g, (idealResidualCopied ν g).card) * (2 * (J + ell)) ≤
      (Fintype.card G * m) * (2 * (J + ell)) := by
  have hs : (∑ g, (idealResidualCopied ν g).card) ≤ Fintype.card G * m := by
    calc
      _ ≤ ∑ _g : G, m := sum_le_sum fun g _ =>
        idealSourceResidualCopied_card_le S T hm ν hν g
      _ = _ := by simp
  exact Nat.mul_le_mul_right _ hs

theorem idealSource_group_count_polynomial {L C₀ : ℝ} {b K : ℕ}
    (hL : 1 ≤ L) (hC₀ : 0 ≤ C₀) (hCL : C₀ ≤ L)
    (hb : (b : ℝ) ≤ C₀ * Real.log L) (hK : (K : ℝ) ≤ L) :
    ((b * K : ℕ) : ℝ) ≤ L ^ (3 : ℕ) := by
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hlog : Real.log L ≤ L :=
    (Real.log_le_sub_one_of_pos hLpos).trans (by linarith)
  have hb2 : (b : ℝ) ≤ L ^ (2 : ℕ) := by
    calc
      _ ≤ C₀ * Real.log L := hb
      _ ≤ C₀ * L := mul_le_mul_of_nonneg_left hlog hC₀
      _ ≤ L * L := mul_le_mul_of_nonneg_right hCL hLpos.le
      _ = _ := by ring
  rw [Nat.cast_mul]
  calc
    _ ≤ L ^ (2 : ℕ) * L := mul_le_mul hb2 hK (Nat.cast_nonneg _) (sq_nonneg L)
    _ = _ := by ring

end
end ArtinMatthews
