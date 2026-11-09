module

public import ArtinMatthews.GiantCandidatePrimeHitProbabilities


set_option backward.privateInPublic true
@[expose] public section

/-! At large primes the predecessor and product hit probabilities have
the required reciprocal lower bounds. -/

namespace ArtinMatthews
noncomputable section

theorem giantCandidatePrimeHitProbability_predecessor_upper (p j : ℕ) [Fact p.Prime] (hj : 0<j) :
    giantCandidatePrimeHitProbability p j .predecessor≤1/(p:ℝ) := by
  have hp := (Fact.out : p.Prime)
  have hpR : (0:ℝ)<p := Nat.cast_pos.mpr hp.pos
  have h₁ : 1/(p:ℝ)≤1 := (div_le_one hpR).mpr (Nat.one_le_cast.mpr hp.one_le)
  rw [giantCandidatePrimeHitProbability_predecessor_ratio p j hj]
  exact div_le_div_of_nonneg_right
    (pow_le_one₀ (sub_nonneg.mpr h₁) (sub_le_self _ (by positivity))) hpR.le

theorem giantCandidatePrimeHitProbability_predecessor_lower (p j : ℕ) [Fact p.Prime] (hj : 0<j)
    (hpj : 2*(j:ℝ)≤p) : 1/(2*(p:ℝ))≤giantCandidatePrimeHitProbability p j .predecessor := by
  have hp := (Fact.out : p.Prime)
  have hpR : (0:ℝ)<p := Nat.cast_pos.mpr hp.pos
  have h₁ : 1/(p:ℝ)≤1 := (div_le_one hpR).mpr (Nat.one_le_cast.mpr hp.one_le)
  have hbern := one_add_mul_le_pow (show (-2:ℝ)≤ -(1/(p:ℝ)) by linarith only [h₁]) (j-1)
  have hJ : ((j-1:ℕ):ℝ)≤j := Nat.cast_le.mpr (Nat.sub_le _ _)
  have hterm : ((j-1:ℕ):ℝ)*(1/(p:ℝ))≤1/2 := by
    rw [mul_one_div]
    apply (div_le_iff₀ hpR).mpr
    linarith only [hpj,hJ]
  have hpow : (1/2:ℝ)≤(1-1/(p:ℝ))^(j-1) := by
    rw [sub_eq_add_neg]
    linarith only [hbern,hterm]
  rw [giantCandidatePrimeHitProbability_predecessor_ratio p j hj]
  calc
    _ = (1/2)/(p:ℝ) := by ring
    _ ≤ _ := div_le_div_of_nonneg_right hpow hpR.le

theorem giantCandidatePrimeHitProbability_product_lower (p j : ℕ) [Fact p.Prime] (hj : 0<j) :
    1/(p:ℝ)≤giantCandidatePrimeHitProbability p j .product := by
  have hp := (Fact.out : p.Prime)
  have hpR : (0:ℝ)<p := Nat.cast_pos.mpr hp.pos
  have h₁ : 1/(p:ℝ)≤1 := (div_le_one hpR).mpr (Nat.one_le_cast.mpr hp.one_le)
  let t := 1-1/(p:ℝ)
  have ht₀ : 0≤t := sub_nonneg.mpr h₁
  have ht₁ : t≤1 := sub_le_self _ (by positivity)
  have hpow : t^j≤t := by
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
    rw [pow_succ]
    exact mul_le_of_le_one_left ht₀ (pow_le_one₀ ht₀ ht₁)
  rw [giantCandidatePrimeHitProbability_product]
  change 1/(p:ℝ)≤1-t^j
  dsimp only [t] at hpow
  change 1/(p:ℝ)≤1-(1-1/(p:ℝ))^j
  linarith only [hpow]

theorem giantCandidate_exp_neg_twice_le_one_sub {u : ℝ} (hu : 0≤u) (hu₁ : u≤1/2) :
    Real.exp (-(2*u))≤1-u := by
  have hden : 0<1-u := by linarith only [hu₁]
  have h : (1-u)⁻¹-1 = u/(1-u) := by
    field_simp [hden.ne']
    ring
  have huDiv : u/(1-u)≤2*u := by
    apply (div_le_iff₀ hden).mpr
    nlinarith only [mul_nonneg hu (show 0≤1-2*u by linarith only [hu₁])]
  have hl := (Real.log_le_sub_one_of_pos (inv_pos.mpr hden)).trans (h.trans_le huDiv)
  rw [Real.log_inv] at hl
  exact (Real.exp_le_exp.mpr (by linarith only [hl])).trans_eq (Real.exp_log hden)

end
end ArtinMatthews
