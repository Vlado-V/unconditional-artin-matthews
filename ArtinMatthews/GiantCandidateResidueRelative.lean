module

public import ArtinMatthews.GiantCandidateResidueFinite
public import ArtinMatthews.GiantCandidateResidueLength
public import ArtinMatthews.MarkedRoughBonferroniBudget
public import ArtinMatthews.MarkedMajorArcRoughLowBudget
public import ArtinMatthews.MarkedMajorArcRoughMertens


set_option backward.privateInPublic true
@[expose] public section

/-! Uniform relative rough residue counts for the actual small-prime
cutoff and candidate modulus range. -/

namespace ArtinMatthews
noncomputable section
open Finset Filter
open scoped BigOperators

theorem giant_candidate_rough_residue_relative_eventually (τ C A c : ℝ)
    (hτ : 0 < τ) (hA : 0 ≤ A) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop,∀ M N Q a : ℕ,0<Q →
      (Q:ℝ) ≤ Real.exp (C*L^(9/20:ℝ)) →
      (∀ p∈Nat.primesLE ⌊Real.exp (L^(6/25:ℝ))⌋₊,p.Coprime Q) →
      Real.exp (τ*L) ≤ ((N-M:ℕ):ℝ) →
      let W := Real.exp (L^(6/25:ℝ))
      let V := markedSieveEulerProduct W
      let H := ((N-M:ℕ):ℝ)/(Q:ℝ)
      |((giantCandidateRoughResidueIoc (Nat.primesLE ⌊W⌋₊) M N Q a).card:ℝ)-H*V| ≤
        (H*V)*(c*L^(-A)) := by
  let K := Real.exp (Real.eulerMascheroniConstant+1)
  obtain ⟨D,hD,hbudget⟩ := marked_rough_bonferroni_uniform_power K (6/25) (τ/2) (6/25) A c
    (by norm_num) hA (half_pos hτ) (by norm_num) hc
  filter_upwards [hbudget,giant_candidate_residue_double_modulus_le_eventually C τ hτ,
    marked_rough_count_endpoint_budget 0 D (6/25) (by norm_num) hD.le (by norm_num),
    marked_rough_density_inverse_cutoff (6/25) (by norm_num),
    marked_rough_prime_reciprocal_cutoff_le (6/25) (by norm_num) (by norm_num),
    eventually_ge_atTop (1:ℝ)] with L htail hmod hdepth hVinv hrec hL
  intro M N Q a hQ hQhi hcop hlen
  let W := Real.exp (L^(6/25:ℝ))
  let V := markedSieveEulerProduct W
  let v := ⌊W⌋₊
  let P := Nat.primesLE v
  let r := ⌊D*Real.log L⌋₊
  let S := ∑ p ∈ P,1/(p:ℝ)
  let F := markedFactorialTail S (r+1)
  let H := ((N-M:ℕ):ℝ)/(Q:ℝ)
  let H' := ((N-M:ℕ):ℝ)/(2*(Q:ℝ))
  have hL₀ : 0 ≤ L := zero_le_one.trans hL
  have hQ₀ : (0:ℝ) < Q := Nat.cast_pos.mpr hQ
  have hlen₀ : (0:ℝ) < ((N-M:ℕ):ℝ) := (Real.exp_pos _).trans_le hlen
  have hMN : M ≤ N := (Nat.sub_pos_iff_lt.mp (Nat.cast_pos.mp hlen₀)).le
  have hH : 0 < H := div_pos hlen₀ hQ₀
  have hV : 0 < V := markedSieveEulerProduct_pos W
  have hS : 0 ≤ S := sum_nonneg (fun _ _ => by positivity)
  have hH' : Real.exp ((τ/2)*L) ≤ H' :=
    giantCandidateResidueLength_le hQ₀ ((mul_le_mul_of_nonneg_left hQhi (by norm_num)).trans hmod) hlen
  have hHhalf : H' = H/2 := by dsimp only [H',H]; ring
  have hW : 0 < W := Real.exp_pos _
  have hv : 1 ≤ v := (Nat.le_floor_iff hW.le).mpr (by
    rw [Nat.cast_one]
    exact Real.one_le_exp_iff.mpr (Real.rpow_nonneg hL₀ _))
  have hp (i : ℕ) : (v:ℝ)^i ≤ W^i :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.floor_le hW.le) i
  have hr : ((r+1:ℕ):ℝ) ≤ W := by
    have h := hdepth 0 (le_refl 0) (by rw [Real.rpow_zero]; norm_num)
    change (0+2)*((r+1:ℕ):ℝ) ≤ W at h
    linarith only [h,Nat.cast_nonneg (α:=ℝ) (r+1)]
  have hlast : ((r+1:ℕ):ℝ)*(v:ℝ)^r ≤ W^(r+1) := by
    calc
      _ ≤ W*W^r := mul_le_mul hr (hp r) (by positivity) hW.le
      _ = _ := (pow_succ' _ _).symm
  have hfinite := giantCandidateRoughResidueIoc_error_numeric P r M N Q a v hMN hQ
    (fun _ hp => Nat.prime_of_mem_primesLE hp) hcop (fun _ hp => (Nat.mem_primesLE.mp hp).1) hv
  change |((giantCandidateRoughResidueIoc P M N Q a).card:ℝ)-H*V| ≤
    2*H*F+(v:ℝ)^(r+1)+((r+1:ℕ):ℝ)*(v:ℝ)^r at hfinite
  have hnum := htail S V H' hS hrec hV (by simpa only [one_div] using hVinv) hH'
  change 2*F/V+W^(r+1)/(H'*V) ≤ c*L^(-A) at hnum
  have he : (H*V)*(2*F/V+W^(r+1)/(H'*V)) = 2*H*F+2*W^(r+1) := by
    rw [hHhalf]
    field_simp [hV.ne',hH.ne']
  change |((giantCandidateRoughResidueIoc P M N Q a).card:ℝ)-H*V| ≤ (H*V)*(c*L^(-A))
  calc
    _ ≤ 2*H*F+(v:ℝ)^(r+1)+((r+1:ℕ):ℝ)*(v:ℝ)^r := hfinite
    _ ≤ 2*H*F+2*W^(r+1) := by linarith only [hp (r+1),hlast]
    _ = (H*V)*(2*F/V+W^(r+1)/(H'*V)) := he.symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hnum (mul_pos hH hV).le

end
end ArtinMatthews
