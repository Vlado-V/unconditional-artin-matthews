module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real


set_option backward.privateInPublic true
@[expose] public section

/-! A sharp positive prefix bound also controls a power-decaying cutoff,
including scales smaller than the first positive index. -/

namespace ArtinMatthews

private theorem spectralDyadicWeight_cover {L : ℝ} (hL : 0 < L)
    (A : ℕ) (hA : 1 ≤ A) (k : ℕ) :
    ∃ j : ℕ, ((k+1 : ℕ) : ℝ) ≤ 2^(j+1)*L ∧
      min 1 ((L/((k+1 : ℕ) : ℝ))^(2*A)) ≤ (1/4 : ℝ)^j := by
  let d : ℝ := (k+1 : ℕ)
  have hd : 0 < d := Nat.cast_pos.mpr (Nat.succ_pos k)
  by_cases h : d ≤ L
  · refine ⟨0, ?_, ?_⟩
    · change d ≤ (2 : ℝ)^(0+1)*L
      norm_num only [zero_add, pow_one]
      linarith
    · simpa only [pow_zero] using (min_le_left 1 ((L/d)^(2*A)))
  have hunit : L/d ≤ 1 := (div_le_one hd).mpr (le_of_not_ge h)
  obtain ⟨j,hlo,hhi⟩ := exists_nat_pow_near
    ((one_le_div hL).mpr (le_of_not_ge h)) (show (1 : ℝ) < 2 by norm_num)
  have hp : 0 < (2 : ℝ)^j := pow_pos two_pos j
  have hratio : L/d ≤ 1/(2 : ℝ)^j := by
    apply (div_le_div_iff₀ hd hp).mpr
    rw [one_mul, mul_comm]
    exact (le_div_iff₀ hL).mp hlo
  refine ⟨j, (div_lt_iff₀ hL).mp hhi |>.le, ?_⟩
  calc
    min 1 ((L/d)^(2*A)) ≤ (L/d)^(2*A) := min_le_right _ _
    _ ≤ (L/d)^2 := pow_le_pow_of_le_one (div_nonneg hL.le hd.le) hunit (by omega)
    _ ≤ (1/(2 : ℝ)^j)^2 := pow_le_pow_left₀ (div_nonneg hL.le hd.le) hratio _
    _ = (1/4 : ℝ)^j := by
      rw [div_pow, one_pow, ← pow_mul, Nat.mul_comm j, pow_mul, ← one_pow j, ← div_pow]
      norm_num

theorem spectral_weighted_prefix_bound (f : ℕ → ℝ) (hf : ∀ k, 0 ≤ f k)
    {C δ L : ℝ} (hC : 0 ≤ C) (hδ : δ ≤ 1) (hL : 0 < L)
    (A : ℕ) (hA : 1 ≤ A)
    (hprefix : ∀ T : ℝ, 0 < T → ∑ k ∈ Finset.range ⌊T⌋₊, f k ≤ C*T^δ) :
    let w (k : ℕ) := f k * min 1 ((L/((k+1 : ℕ) : ℝ))^(2*A))
    Summable w ∧ ∑' k, w k ≤ 4*C*L^δ := by
  classical
  dsimp only
  let T (i : ℕ) : ℝ := 2^(i+1)*L
  let a (i : ℕ) : ℝ := (1/4)^i
  let g (i k : ℕ) : ℝ := if k < ⌊T i⌋₊ then a i*f k else 0
  have hT (i : ℕ) : 0 < T i := mul_pos (pow_pos two_pos _) hL
  have ha (i : ℕ) : 0 ≤ a i := pow_nonneg (by norm_num) _
  have hg (i k : ℕ) : 0 ≤ g i k := by
    dsimp only [g]
    split
    · exact mul_nonneg (ha i) (hf k)
    · exact le_rfl
  have hw (k : ℕ) : 0 ≤ f k * min 1 ((L/((k+1 : ℕ) : ℝ))^(2*A)) :=
    mul_nonneg (hf k) (le_min zero_le_one (pow_nonneg (div_nonneg hL.le (Nat.cast_nonneg _)) _))
  choose j hcut hweight using fun k => spectralDyadicWeight_cover hL A hA k
  have hfinite (K : ℕ) :
      (∑ k ∈ Finset.range K, f k * min 1 ((L/((k+1 : ℕ) : ℝ))^(2*A))) ≤ 4*C*L^δ := by
    let J := (Finset.range K).sup j + 1
    have hgeom : (∑ i ∈ Finset.range J, (1/2 : ℝ)^i) ≤ 2 := by
      calc
        _ ≤ ∑' i : ℕ, (1/2 : ℝ)^i :=
          (summable_geometric_of_lt_one (by norm_num) (by norm_num)).sum_le_tsum _
            (fun i _ => pow_nonneg (by norm_num) i)
        _ = _ := by rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; norm_num
    calc
      _ ≤ ∑ k ∈ Finset.range K, ∑ i ∈ Finset.range J, g i k := by
        apply Finset.sum_le_sum
        intro k hk
        have hj : j k ∈ Finset.range J :=
          Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup hk))
        have hkj : k < ⌊T (j k)⌋₊ :=
          Nat.lt_of_succ_le ((Nat.le_floor_iff' (Nat.succ_ne_zero k)).mpr (hcut k))
        calc
          _ ≤ g (j k) k := by
            rw [show g (j k) k = a (j k)*f k from ite_eq_left hkj]
            exact (mul_le_mul_of_nonneg_left (hweight k) (hf k)).trans_eq (mul_comm _ _)
          _ ≤ _ := Finset.single_le_sum (fun i _ => hg i k) hj
      _ = ∑ i ∈ Finset.range J, ∑ k ∈ Finset.range K, g i k := Finset.sum_comm
      _ ≤ ∑ i ∈ Finset.range J, a i*(C*(T i)^δ) := by
        apply Finset.sum_le_sum
        intro i _
        calc
          _ = ∑ k ∈ (Finset.range K).filter (fun k => k < ⌊T i⌋₊), a i*f k :=
            (Finset.sum_filter _ _).symm
          _ ≤ ∑ k ∈ Finset.range ⌊T i⌋₊, a i*f k :=
            Finset.sum_le_sum_of_subset_of_nonneg
              (fun k hk => Finset.mem_range.mpr (Finset.mem_filter.mp hk).2)
              (fun k _ _ => mul_nonneg (ha i) (hf k))
          _ ≤ _ := by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (hprefix _ (hT i)) (ha i)
      _ ≤ ∑ i ∈ Finset.range J, (2*C*L^δ)*(1/2 : ℝ)^i := by
        apply Finset.sum_le_sum
        intro i _
        have hpow : 1 ≤ (2 : ℝ)^(i+1) := one_le_pow₀ (by norm_num)
        have hscale : (T i)^δ ≤ (2 : ℝ)^(i+1)*L^δ := by
          dsimp only [T]
          rw [Real.mul_rpow (by positivity) hL.le]
          exact mul_le_mul_of_nonneg_right (Real.rpow_le_self_of_one_le hpow hδ) (Real.rpow_nonneg hL.le _)
        calc
          _ ≤ a i*(C*(2^(i+1)*L^δ)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hscale hC) (ha i)
          _ = _ := by
            dsimp only [a]
            rw [pow_succ, show (1/2 : ℝ) = (1/4)*2 by norm_num, mul_pow]
            ring
      _ ≤ _ := by
        rw [← Finset.mul_sum]
        calc
          _ ≤ (2*C*L^δ)*2 := mul_le_mul_of_nonneg_left hgeom (by positivity)
          _ = _ := by ring
  exact ⟨summable_of_sum_range_le hw hfinite, Real.tsum_le_of_sum_range_le hw hfinite⟩

end ArtinMatthews
