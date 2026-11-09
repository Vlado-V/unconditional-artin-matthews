module

public import ArtinMatthews.MarkedMajorPrimeDyads


set_option backward.privateInPublic true
@[expose] public section

/-! The ordinary dyadic partition costs only a fixed power of the logarithm,
and every occupied dyad retains the exact sparse-prime scale window. -/
namespace ArtinMatthews
open Finset Filter
open scoped Topology

 theorem markedMajorPrimeDyads_uniform (c C : ℝ) (hc : 0 < c) (hC : 0 < C) :
    ∀ᶠ L : ℝ in atTop,∀ S : Finset ℕ,
      (∀ p ∈ S,p.Prime) →
      (∀ p ∈ S,c*L^(1/(10:ℝ)) ≤ Real.log p) →
      (∀ p ∈ S,Real.log p ≤ C*L^(1/(5:ℝ))) →
      ((markedMajorPrimeDyadIndices S).card:ℝ) ≤ (1+C/Real.log 2)*L ∧
      ∀ j ∈ markedMajorPrimeDyadIndices S,
        1 < ((2:ℕ)^j:ℝ) ∧ (c/2)*L^(1/(10:ℝ)) ≤ Real.log (((2:ℕ)^j:ℝ)) ∧
          Real.log (((2:ℕ)^j:ℝ)) ≤ C*L^(1/(5:ℝ)) := by
  have ht := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/10)).eventually
    (eventually_ge_atTop (2*Real.log 2/c))
  filter_upwards [ht,eventually_ge_atTop (1:ℝ)] with L hlarge hL
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  intro S hS hlo hhi
  have hZ : 1 ≤ Real.exp (C*L^(1/(5:ℝ))) := Real.one_le_exp (by positivity)
  have hcap : ∀ p ∈ S,(p:ℝ) ≤ Real.exp (C*L^(1/(5:ℝ))) := by
    intro p hp
    exact (Real.log_le_iff_le_exp (by exact_mod_cast (hS p hp).pos)).mp (hhi p hp)
  have hcard := markedMajorPrimeDyadIndices_card S _ hZ hcap
  rw [Real.log_exp] at hcard
  refine ⟨?_,?_⟩
  · have hp : L^(1/(5:ℝ)) ≤ L := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hL (by norm_num : (1/(5:ℝ))≤1)
    have hh := mul_le_mul_of_nonneg_left hp (div_pos hC hlog2).le
    calc
      _ ≤ 1+C*L^(1/(5:ℝ))/Real.log 2 := hcard
      _ ≤ (1+C/Real.log 2)*L := by
        have he : C*L^(1/(5:ℝ))/Real.log 2 = (C/Real.log 2)*L^(1/(5:ℝ)) := by ring
        rw [he]
        nlinarith
  · intro j hj
    obtain ⟨hY,hl,hh⟩ := markedMajorPrimeDyad_log_bounds S j _ _ hS hlo hhi hj
    have hlog : 2*Real.log 2 ≤ c*L^(1/(10:ℝ)) := by
      exact (div_le_iff₀ hc).mp hlarge |>.trans_eq (mul_comm _ _)
    exact ⟨hY,by nlinarith,hh⟩

end ArtinMatthews
