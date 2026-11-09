module

public import ArtinMatthews.MarkedBirthRankSums
public import ArtinMatthews.MarkedBirthRankCutoff
public import Mathlib.Analysis.Complex.Norm


set_option backward.privateInPublic true
@[expose] public section

/-! The final finite triangle inequality and the existing one-power
margin combine low and high ranks without discarding a signed edge
estimate before the rank decomposition. -/

noncomputable section
namespace ArtinMatthews
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem markedBirthPermutationSign_norm {A : Type*} [Fintype A] [DecidableEq A]
    (σ : Equiv.Perm A) : ‖((σ.sign:ℤ):ℂ)‖=1 := by
  rcases Int.units_eq_one_or σ.sign with h | h <;> simp only [h,Units.val_one,Units.val_neg,
    Int.cast_one,Int.cast_neg,norm_one,norm_neg]

theorem markedBirthSignedSum_norm_le {A : Type*} [Fintype A] [DecidableEq A]
    (F : Equiv.Perm A → ℂ) :
    ‖∑ σ,((σ.sign:ℤ):ℂ)*F σ‖ ≤ ∑ σ,‖F σ‖ := by
  refine (norm_sum_le _ _).trans_eq ?_
  apply Finset.sum_congr rfl
  intro σ _
  rw [norm_mul,markedBirthPermutationSign_norm,one_mul]

theorem markedBirthRank_norm_split {A : Type*} [Fintype A] [DecidableEq A]
    (F : Equiv.Perm A → ℂ) (r₀ : ℕ) :
    (∑ σ,‖F σ‖)=
      (∑ σ,if markedBirthPermutationRank σ<r₀ then ‖F σ‖ else 0)+
        ∑ σ,if r₀ ≤ markedBirthPermutationRank σ then ‖F σ‖ else 0 := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro σ _
  by_cases h : markedBirthPermutationRank σ<r₀
  · rw [ite_eq_left h,ite_eq_right (by omega),add_zero]
  · rw [ite_eq_right h,ite_eq_left (by omega),zero_add]

theorem markedBirth_rank_pair_budget (G : ℝ) :
    ∀ᶠ x : ℝ in atTop,
      2*((Real.log x)^(-(G+1)))^(markedMemoryMomentLength x) ≤
        ((Real.log x)^(-G))^(markedMemoryMomentLength x) := by
  filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (2:ℝ))] with x hlog
  let L := Real.log x
  let N := markedMemoryMomentLength x
  have hL₂ : 2 ≤ L := hlog
  have hL₁ : 1 ≤ L := by linarith
  have hL : 0 < L := by linarith
  have hNreal : 1 ≤ (N:ℝ) :=
    (Real.one_le_rpow hL₁ (by norm_num : (0:ℝ) ≤ 1/2)).trans (markedMemoryMomentLength_lower hL.le)
  have hN : 1 ≤ N := by exact_mod_cast hNreal
  have htwo : (2:ℝ) ≤ L^N := hL₂.trans (by simpa only [pow_one] using pow_le_pow_right₀ hL₁ hN)
  have hmul : L*L^(-(G+1))=L^(-G) := by
    calc
      _ = L^(1:ℝ)*L^(-(G+1)) := congrArg (fun t => t*L^(-(G+1))) (Real.rpow_one L).symm
      _ = _ := by rw [← Real.rpow_add hL]; congr 1; ring
  calc
    _ ≤ L^N*(L^(-(G+1)))^N := mul_le_mul_of_nonneg_right htwo
      (pow_nonneg (Real.rpow_nonneg hL.le _) _)
    _ = _ := by rw [← mul_pow,hmul]

end ArtinMatthews
