module

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Tactic


set_option backward.privateInPublic true
@[expose] public section

/-! Geometric sums with the exact diagonal and strict support conditions of
the local C_{t,k}(6r) table.  Only the products that are actually summed are
required to have norm less than one. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open scoped BigOperators Classical
noncomputable section

theorem probe_geometric_strict_tail (V : ℂ) (hV : ‖V‖ < 1) (d : ℕ) :
    (∑' r : ℕ, if d < r then V ^ r else 0) = V ^ (d + 1) / (1 - V) := by
  let f : ℕ → ℂ := fun r => if d < r then V ^ r else 0
  have hi : Function.Injective (fun n : ℕ => n + (d + 1)) :=
    fun _ _ h => Nat.add_right_cancel h
  have hs : Function.support f ⊆ Set.range (fun n : ℕ => n + (d + 1)) := by
    intro r hr
    have hd : d < r := by
      by_contra hn
      exact hr (by simp [f, hn])
    exact ⟨r - (d + 1), Nat.sub_add_cancel (by omega)⟩
  have he := hi.tsum_eq hs
  calc
    _ = ∑' n : ℕ, V ^ (n + (d + 1)) := by
      rw [← he]
      apply tsum_congr
      intro n
      exact ite_eq_left (by omega)
    _ = V ^ (d + 1) * ∑' n : ℕ, V ^ n := by
      simp only [pow_add]
      rw [tsum_mul_right, mul_comm]
    _ = _ := by rw [tsum_geometric_of_norm_lt_one hV, div_eq_mul_inv]

theorem probe_geometric_diagonal (R V : ℂ) (hRV : ‖R * V‖ < 1) :
    (∑' d : ℕ, ∑' r : ℕ, if r = d then R ^ d * V ^ r else 0) =
      1 / (1 - R * V) := by
  simp only [tsum_ite_eq, ← mul_pow]
  rw [tsum_geometric_of_norm_lt_one hRV, one_div]

theorem probe_geometric_successor_diagonal (R V : ℂ) (hRV : ‖R * V‖ < 1) :
    (∑' d : ℕ, ∑' r : ℕ, if r = d + 1 then R ^ (d + 1) * V ^ r else 0) =
      (R * V) / (1 - R * V) := by
  simp only [tsum_ite_eq]
  simp_rw [← mul_pow, pow_succ]
  rw [tsum_mul_right, tsum_geometric_of_norm_lt_one hRV, div_eq_mul_inv, mul_comm]

theorem probe_geometric_strict_double (R V : ℂ) (hV : ‖V‖ < 1)
    (hRV : ‖R * V‖ < 1) :
    (∑' d : ℕ, ∑' r : ℕ, if d < r then R ^ d * V ^ r else 0) =
      V / ((1 - R * V) * (1 - V)) := by
  have hi (d : ℕ) : (∑' r : ℕ, if d < r then R ^ d * V ^ r else 0) =
      R ^ d * (V ^ (d + 1) / (1 - V)) := by
    rw [← probe_geometric_strict_tail V hV d, ← tsum_mul_left]
    apply tsum_congr
    intro r
    split_ifs <;> simp
  simp_rw [hi, pow_succ]
  calc
    _ = ∑' d : ℕ, (R * V) ^ d * (V / (1 - V)) := by
      apply tsum_congr
      intro d
      rw [mul_pow]
      ring
    _ = _ := by
      rw [tsum_mul_right, tsum_geometric_of_norm_lt_one hRV]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

theorem probe_geometric_strict_successor_double (R V : ℂ) (hV : ‖V‖ < 1)
    (hRV : ‖R * V‖ < 1) :
    (∑' d : ℕ, ∑' r : ℕ, if d < r then R ^ (d + 1) * V ^ r else 0) =
      (R * V) / ((1 - R * V) * (1 - V)) := by
  have he : (∑' d : ℕ, ∑' r : ℕ, if d < r then R ^ (d + 1) * V ^ r else 0) =
      R * (∑' d : ℕ, ∑' r : ℕ, if d < r then R ^ d * V ^ r else 0) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro d
    rw [← tsum_mul_left]
    apply tsum_congr
    intro r
    split_ifs
    · rw [pow_succ]
      ring
    · simp
  rw [he, probe_geometric_strict_double R V hV hRV]
  ring

end

end ArtinMatthews.VaryingKummerAnalytic
