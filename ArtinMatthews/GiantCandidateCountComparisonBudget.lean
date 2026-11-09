module

public import ArtinMatthews.GiantCandidateCountMeanRemainder
public import Mathlib.Topology.Algebra.Order.Floor


set_option backward.privateInPublic true
@[expose] public section

/-! The count cutoff, Bonferroni depth, and moment precision can all
be fixed before the asymptotic parameter is taken to infinity. -/

namespace ArtinMatthews
noncomputable section
open Finset Filter
open scoped BigOperators Topology

def giantCandidateCountPolyCost (ι : Type*) [Fintype ι] [DecidableEq ι] (a b : ℕ) : ℝ :=
  ∑ k∈giantCandidateCountVectors ι a,
    ∑ l∈giantCandidateCountVectors ι (2*b),|giantCandidateCountPolyCoeff k l|

theorem giantCandidateCountRemainderScale_tendsto (C : ℝ) (a : ℕ) :
    Tendsto (fun b : ℕ => giantCandidateCountRemainderScale C a (2*b+1)) atTop (𝓝 0) := by
  have hmap : Tendsto (fun b : ℕ => 2*b+1) atTop atTop := by
    apply tendsto_atTop.2
    intro k
    filter_upwards [eventually_ge_atTop k] with b hb
    omega
  have h := ((FloorSemiring.tendsto_pow_div_factorial_atTop C).comp hmap).const_mul ((max 1 C)^a)
  simpa only [Function.comp_apply,giantCandidateCountRemainderScale,mul_zero] using h

theorem giantCandidateCountComparisonBudget (ι : Type*) [Fintype ι] [DecidableEq ι]
    {C δ : ℝ} (hδ : 0<δ) :
    ∃ a b : ℕ,∃ η : ℝ,0<η ∧
      2*C*(Fintype.card ι:ℝ)/((a:ℝ)+1)≤δ/6 ∧
      giantCandidateCountRemainderScale C a (2*b+1)≤1 ∧
      2*((giantCandidateCountVectors ι a).card:ℝ)*
        (2*(2:ℝ)^Fintype.card ι*giantCandidateCountRemainderScale C a (2*b+1))≤δ/3 ∧
      giantCandidateCountPolyCost ι a b*η≤δ/3 := by
  obtain ⟨a,ha⟩ := exists_nat_gt (12*C*(Fintype.card ι:ℝ)/δ)
  have htail : 2*C*(Fintype.card ι:ℝ)/((a:ℝ)+1)≤δ/6 := by
    apply (div_le_iff₀ (by positivity : 0 < (a:ℝ)+1)).mpr
    have h := (div_lt_iff₀ hδ).mp ha
    nlinarith only [h,hδ]
  let K := 2*(2:ℝ)^Fintype.card ι
  let E := giantCandidateCountVectors ι a
  let d := δ/(6*((E.card:ℝ)+1))
  have hK : 0<K := by dsimp only [K]; positivity
  have hE : 0<(E.card:ℝ)+1 := by positivity
  have hd : 0<d := div_pos hδ (mul_pos (by norm_num) hE)
  obtain ⟨b,hb⟩ := ((giantCandidateCountRemainderScale_tendsto C a).eventually
    (Iio_mem_nhds (lt_min (by norm_num : (0:ℝ)<1) (div_pos hd hK)))).exists
  have hb₁ : giantCandidateCountRemainderScale C a (2*b+1)≤1 :=
    ((lt_min_iff.mp hb).1).le
  have hbm : K*giantCandidateCountRemainderScale C a (2*b+1)≤d := by
    calc
      _ ≤ K*(d/K) := mul_le_mul_of_nonneg_left ((lt_min_iff.mp hb).2).le hK.le
      _ = _ := by rw [mul_comm,div_mul_cancel₀ _ hK.ne']
  have hpoint : 2*(E.card:ℝ)*(K*giantCandidateCountRemainderScale C a (2*b+1))≤δ/3 := by
    calc
      _ ≤ 2*(E.card:ℝ)*d := mul_le_mul_of_nonneg_left hbm (by positivity)
      _ ≤ 2*((E.card:ℝ)+1)*d := mul_le_mul_of_nonneg_right (by linarith) hd.le
      _ = _ := by
        dsimp only [d]
        field_simp [hE.ne']
        norm_num
  let P := giantCandidateCountPolyCost ι a b
  let η := δ/(3*(P+1))
  have hP : 0≤P := sum_nonneg (fun _ _ => sum_nonneg (fun _ _ => abs_nonneg _))
  have hP₁ : 0<P+1 := by linarith
  have hη : 0<η := div_pos hδ (mul_pos (by norm_num) hP₁)
  refine ⟨a,b,η,hη,htail,hb₁,hpoint,?_⟩
  change P*η≤δ/3
  calc
    _ ≤ (P+1)*η := mul_le_mul_of_nonneg_right (by linarith) hη.le
    _ = _ := by
      dsimp only [η]
      field_simp [hP₁.ne']

end
end ArtinMatthews
