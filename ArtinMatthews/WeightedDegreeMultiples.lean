module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Tactic


set_option backward.privateInPublic true
@[expose] public section

/-! A finite change of variables between positive exponents and positive
degree multiples. This is the arithmetic regrouping in the Euler recurrence. -/
namespace ArtinMatthews.WeightedMonic
open scoped BigOperators

 theorem sum_degree_multiples (d n : ℕ) (hd : 0 < d) (f : ℕ → ℕ → ℂ) :
    (∑ r ∈ Finset.Icc 1 n, if r*d ≤ n then f r (r*d) else 0) =
      ∑ k ∈ Finset.Icc 1 n, if d ∣ k then f (k/d) k else 0 := by
  classical
  rw [←Finset.sum_filter,←Finset.sum_filter]
  apply Finset.sum_bij (fun r _ => r*d)
  · intro r hr
    obtain ⟨hr,hrn⟩ := Finset.mem_filter.mp hr
    obtain ⟨hr1,_hrn⟩ := Finset.mem_Icc.mp hr
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.mul_pos hr1 hd,hrn⟩,dvd_mul_left d r⟩
  · intro r hr s hs he
    exact mul_right_cancel₀ (Nat.ne_of_gt hd) he
  · intro k hk
    obtain ⟨hk,hdiv⟩ := Finset.mem_filter.mp hk
    obtain ⟨hk1,hkn⟩ := Finset.mem_Icc.mp hk
    have he : (k/d)*d = k := Nat.div_mul_cancel hdiv
    have hr1 : 1 ≤ k/d := Nat.div_pos (Nat.le_of_dvd hk1 hdiv) hd
    have hrr : k/d ≤ (k/d)*d := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left (k/d) hd
    exact ⟨k/d,Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hr1,hrr.trans (he.trans_le hkn)⟩,he.trans_le hkn⟩,he⟩
  · intro r _hr
    rw [Nat.mul_div_cancel r hd]

end ArtinMatthews.WeightedMonic
