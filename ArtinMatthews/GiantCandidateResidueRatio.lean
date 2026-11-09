module

public import ArtinMatthews.GiantCandidateResidueRelative


set_option backward.privateInPublic true
@[expose] public section

/-! Normalize by the actual rough interval cardinality, using the
modulus-one instance of the same relative count. -/

namespace ArtinMatthews
noncomputable section
open Finset Filter

def giantCandidateRoughIoc (P : Finset ℕ) (M N : ℕ) : Finset ℕ :=
  (Ioc M N).filter (fun n => ∀ p∈P,¬p∣n)

theorem giantCandidateRoughResidueIoc_one (P : Finset ℕ) (M N a : ℕ) :
    giantCandidateRoughResidueIoc P M N 1 a = giantCandidateRoughIoc P M N := by
  ext n
  simp only [giantCandidateRoughResidueIoc,giantCandidateRoughIoc,mem_filter,
    Nat.ModEq,Nat.mod_one,eq_self,and_true]

private theorem giantCandidateRelativeQuotient_error {a b H Q ε : ℝ}
    (hH : 0 < H) (hQ : 0 < Q) (hε : 0 ≤ ε) (hε₁ : ε ≤ 1/4)
    (ha : |a-H/Q| ≤ (H/Q)*ε) (hb : |b-H| ≤ H*ε) :
    H/2 ≤ b ∧ b ≤ 2*H ∧ |Q*a/b-1| ≤ 4*ε := by
  have hsm := mul_le_mul_of_nonneg_left hε₁ hH.le
  have hlo : H/2 ≤ b := by linarith only [(abs_le.mp hb).1,hsm,hH.le]
  have hhi : b ≤ 2*H := by linarith only [(abs_le.mp hb).2,hsm,hH.le]
  have hb₀ : 0 < b := (half_pos hH).trans_le hlo
  have hQcancel : Q*(H/Q) = H := by rw [mul_comm,div_mul_cancel₀ _ hQ.ne']
  have hqa : |Q*a-H| ≤ H*ε := by
    calc
      _ = |Q*(a-H/Q)| := by rw [mul_sub,hQcancel]
      _ = Q*|a-H/Q| := by rw [abs_mul,abs_of_pos hQ]
      _ ≤ Q*((H/Q)*ε) := mul_le_mul_of_nonneg_left ha hQ.le
      _ = _ := by rw [← mul_assoc,hQcancel]
  have hdiff : |Q*a-b| ≤ 2*H*ε := by
    calc
      _ = |(Q*a-H)+(H-b)| := by rw [sub_add_sub_cancel]
      _ ≤ |Q*a-H|+|H-b| := abs_add_le _ _
      _ ≤ H*ε+H*ε := add_le_add hqa (by rw [abs_sub_comm]; exact hb)
      _ = _ := by ring
  refine ⟨hlo,hhi,?_⟩
  have he : Q*a/b-1 = (Q*a-b)/b := by rw [sub_div,div_self hb₀.ne']
  rw [he,abs_div,abs_of_pos hb₀]
  apply (div_le_iff₀ hb₀).mpr
  calc
    _ ≤ 2*H*ε := hdiff
    _ = (4*ε)*(H/2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hlo (mul_nonneg (by norm_num) hε)

theorem giant_candidate_rough_residue_ratio_eventually (τ C A : ℝ)
    (hτ : 0 < τ) (hC : 0 ≤ C) (hA : 0 ≤ A) :
    ∀ᶠ L : ℝ in atTop,∀ M N Q a : ℕ,0<Q →
      (Q:ℝ) ≤ Real.exp (C*L^(9/20:ℝ)) →
      (∀ p∈Nat.primesLE ⌊Real.exp (L^(6/25:ℝ))⌋₊,p.Coprime Q) →
      Real.exp (τ*L) ≤ ((N-M:ℕ):ℝ) →
      let W := Real.exp (L^(6/25:ℝ))
      let P := Nat.primesLE ⌊W⌋₊
      let H := ((N-M:ℕ):ℝ)*markedSieveEulerProduct W
      let b := ((giantCandidateRoughIoc P M N).card:ℝ)
      let aQ := ((giantCandidateRoughResidueIoc P M N Q a).card:ℝ)
      H/2 ≤ b ∧ b ≤ 2*H ∧ |(Q:ℝ)*aQ/b-1| ≤ L^(-A) := by
  filter_upwards [giant_candidate_rough_residue_relative_eventually τ C A (1/4)
    hτ hA (by norm_num),eventually_ge_atTop (1:ℝ)] with L hrelative hL
  intro M N Q a hQ hQbound hcop hlen
  let W := Real.exp (L^(6/25:ℝ))
  let P := Nat.primesLE ⌊W⌋₊
  let V := markedSieveEulerProduct W
  let H := ((N-M:ℕ):ℝ)*V
  let b := ((giantCandidateRoughIoc P M N).card:ℝ)
  let aQ := ((giantCandidateRoughResidueIoc P M N Q a).card:ℝ)
  let ε := (1/4:ℝ)*L^(-A)
  have hL₀ : 0 ≤ L := zero_le_one.trans hL
  have hH : 0 < H := mul_pos ((Real.exp_pos _).trans_le hlen) (markedSieveEulerProduct_pos W)
  have hε : 0 ≤ ε := mul_nonneg (by norm_num) (Real.rpow_nonneg hL₀ _)
  have hε₁ : ε ≤ 1/4 := by
    apply mul_le_of_le_one_right (by norm_num : (0:ℝ)≤1/4)
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hL (neg_nonpos.mpr hA)
  have hQ₁ : (1:ℝ) ≤ Real.exp (C*L^(9/20:ℝ)) :=
    Real.one_le_exp_iff.mpr (mul_nonneg hC (Real.rpow_nonneg hL₀ _))
  have hb : |b-H| ≤ H*ε := by
    have h := hrelative M N 1 0 Nat.zero_lt_one (by simpa only [Nat.cast_one] using hQ₁)
      (fun p _ => Nat.coprime_one_right p) hlen
    simpa only [Nat.cast_one,div_one,giantCandidateRoughResidueIoc_one] using h
  have ha : |aQ-H/(Q:ℝ)| ≤ (H/(Q:ℝ))*ε := by
    have h := hrelative M N Q a hQ hQbound hcop hlen
    change |aQ-(((N-M:ℕ):ℝ)/(Q:ℝ))*V| ≤ ((((N-M:ℕ):ℝ)/(Q:ℝ))*V)*ε at h
    have he : (((N-M:ℕ):ℝ)/(Q:ℝ))*V = H/(Q:ℝ) := by dsimp only [H]; ring
    rwa [he] at h
  have h := giantCandidateRelativeQuotient_error hH (Nat.cast_pos.mpr hQ) hε hε₁ ha hb
  change H/2 ≤ b ∧ b ≤ 2*H ∧ |(Q:ℝ)*aQ/b-1| ≤ L^(-A)
  exact ⟨h.1,h.2.1,h.2.2.trans_eq (by dsimp only [ε]; ring)⟩

end
end ArtinMatthews
