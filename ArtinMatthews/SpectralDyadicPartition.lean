module

public import ArtinMatthews.SpectralDyadicWeight
public import Mathlib.Analysis.SpecialFunctions.Pow.Real


set_option backward.privateInPublic true
@[expose] public section

/-! Exact dyadic partition with two overlapping families of the same
smooth function supported in [1,2]. -/
namespace ArtinMatthews

open Filter
open scoped BigOperators Topology
noncomputable section

def spectralDyadicBlock (k : ℕ) (x : ℝ) : ℝ :=
  spectralDyadicWeight (x/(2 : ℝ)^k) +
    spectralDyadicWeight (spectralDyadicRatio*x/(2 : ℝ)^k)

lemma spectralDyadicBlock_nonneg (k : ℕ) (x : ℝ) : 0 ≤ spectralDyadicBlock k x :=
  add_nonneg (spectralDyadicWeight_nonneg _) (spectralDyadicWeight_nonneg _)

lemma spectralDyadicBlock_eq (k : ℕ) (x : ℝ) :
    spectralDyadicBlock k x =
      spectralDyadicStep (spectralDyadicRatio*x/(2 : ℝ)^k) -
        spectralDyadicStep (x/(spectralDyadicRatio*(2 : ℝ)^k)) := by
  have hp : (2 : ℝ)^k ≠ 0 := by positivity
  have hr := spectralDyadicRatio_pos.ne'
  have h₁ : (spectralDyadicRatio*x/(2 : ℝ)^k)/spectralDyadicRatio = x/(2 : ℝ)^k := by
    field_simp
  have h₂ : (x/(2 : ℝ)^k)/spectralDyadicRatio =
      x/(spectralDyadicRatio*(2 : ℝ)^k) := by ring
  unfold spectralDyadicBlock spectralDyadicWeight
  rw [h₁,h₂]
  ring

lemma spectralDyadicBlock_partial_sum (K : ℕ) (x : ℝ) :
    (∑ k ∈ Finset.range (K+1), spectralDyadicBlock k x) =
      spectralDyadicStep (spectralDyadicRatio*x) -
        spectralDyadicStep (x/(spectralDyadicRatio*(2 : ℝ)^K)) := by
  induction K with
  | zero => simp [spectralDyadicBlock_eq]
  | succ K ih =>
    rw [Finset.sum_range_succ,ih,spectralDyadicBlock_eq]
    have hp : (2 : ℝ)^(K+1) ≠ 0 := by positivity
    have hq : spectralDyadicRatio*(2 : ℝ)^K ≠ 0 :=
      mul_ne_zero spectralDyadicRatio_pos.ne' (by positivity)
    have he : spectralDyadicRatio*x/(2 : ℝ)^(K+1) =
        x/(spectralDyadicRatio*(2 : ℝ)^K) := by
      apply (div_eq_div_iff hp hq).2
      have hr : spectralDyadicRatio*spectralDyadicRatio = 2 := by
        nlinarith [spectralDyadicRatio_sq]
      calc
        _ = (spectralDyadicRatio*spectralDyadicRatio)*x*(2 : ℝ)^K := by ring
        _ = _ := by rw [hr,pow_succ]; ring
    rw [he]
    ring

theorem spectralDyadicBlock_partition (n K : ℕ) (hn : 1 ≤ n)
    (hK : (n : ℝ) ≤ (2 : ℝ)^K) :
    (∑ k ∈ Finset.range (K+1), spectralDyadicBlock k n) = 1 := by
  rw [spectralDyadicBlock_partial_sum,spectralDyadicStep_one,spectralDyadicStep_zero]
  · norm_num
  · apply (div_le_one (mul_pos spectralDyadicRatio_pos (by positivity))).2
    apply hK.trans
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      spectralDyadicRatio_one_lt.le (show (0 : ℝ) ≤ 2^K from by positivity)
  · have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hn' spectralDyadicRatio_pos.le

theorem hasSum_spectralDyadicBlock (n : ℕ) (hn : 1 ≤ n) :
    HasSum (fun k => spectralDyadicBlock k n) 1 := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun k => spectralDyadicBlock_nonneg k n) 1).2
  apply (tendsto_add_atTop_iff_nat 1).1
  have ht : Tendsto (fun K : ℕ => (2 : ℝ)^K) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have he : ∀ᶠ K in atTop, (∑ k ∈ Finset.range (K+1), spectralDyadicBlock k n) = 1 := by
    filter_upwards [ht.eventually_ge_atTop (n : ℝ)] with K hK
    exact spectralDyadicBlock_partition n K hn hK
  exact tendsto_const_nhds.congr' (he.mono (fun _ h => h.symm))

end
end ArtinMatthews
