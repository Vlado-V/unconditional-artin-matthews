module

public import ArtinMatthews.ScalarWeightedResidueCRT
public import ArtinMatthews.RoughCharacterDensity


set_option backward.privateInPublic true
@[expose] public section

/-! Absolute weighted Bonferroni errors with the exact finite CRT endpoint cost. -/

namespace ArtinMatthews
open Finset
open OAI.Erdos970.NumberTheoryLean.BonferroniDensity
open scoped BigOperators
noncomputable section

theorem scalarBonferroni_abs_error (P : Finset ℕ) (g : ℕ → ℝ)
    (hg0 : ∀ p ∈ P, 0 ≤ g p) (hg1 : ∀ p ∈ P, g p ≤ 1) (r : ℕ) :
    |densityPolynomial r P g - ∏ p ∈ P, (1 - g p)| ≤ elementarySum P g (r + 1) := by
  rcases Nat.mod_two_eq_zero_or_one r with hmod | hmod
  · have hr : r = 2 * (r / 2) := by omega
    have hb := densityPolynomial_bounds P g hg0 hg1 (r / 2)
    rw [hr, abs_of_nonneg (sub_nonneg.mpr hb.2)]
    calc
      _ ≤ densityPolynomial (2 * (r / 2)) P g -
          densityPolynomial (2 * (r / 2) + 1) P g := sub_le_sub_left hb.1 _
      _ = _ := densityPolynomial_gap (r / 2) P g
  · have hr : r = 2 * (r / 2) + 1 := by omega
    have hb := densityPolynomial_bounds P g hg0 hg1 (r / 2)
    have hnext := (densityPolynomial_bounds P g hg0 hg1 (r / 2 + 1)).2
    rw [hr, abs_of_nonpos (sub_nonpos.mpr hb.1), neg_sub]
    calc
      _ ≤ densityPolynomial (2 * (r / 2 + 1)) P g -
          densityPolynomial (2 * (r / 2) + 1) P g := sub_le_sub_right hnext _
      _ = _ := by
        rw [show 2 * (r / 2 + 1) = (2 * (r / 2) + 1) + 1 by omega,
          densityPolynomial_succ]
        norm_num [pow_add, pow_mul]

def scalarWeightedResidueCount (P : Finset ℕ) (f : ℕ → ℕ → ℝ)
    (lo hi Q a : ℕ) : ℝ :=
  ∑ n ∈ scalarForcedResidueInterval lo hi Q a,
    ∏ p ∈ P, (1 - scalarWeightedResidueLoss f p n)

def scalarWeightedResidueTruncation (P : Finset ℕ) (f : ℕ → ℕ → ℝ)
    (r lo hi Q a : ℕ) : ℝ :=
  ∑ n ∈ scalarForcedResidueInterval lo hi Q a,
    densityPolynomial r P (fun p => scalarWeightedResidueLoss f p n)

def scalarWeightedResidueEndpointMass (P : Finset ℕ) (f : ℕ → ℕ → ℝ) (h : ℕ) : ℝ :=
  ∑ k ∈ range (h + 1), elementarySum P (scalarWeightedResidueMass f) k

theorem scalarWeightedResidueEndpointMass_eq_subsets
    (P : Finset ℕ) (f : ℕ → ℕ → ℝ) (h : ℕ) :
    scalarWeightedResidueEndpointMass P f h =
      ∑ S ∈ roughTruncationSubsets P h, ∏ p ∈ S, scalarWeightedResidueMass f p := by
  simpa only [scalarWeightedResidueEndpointMass, elementarySum] using
    (sum_roughTruncationSubsets P h (fun S => ∏ p ∈ S, scalarWeightedResidueMass f p)).symm

def scalarWeightedResidueCountIco (P : Finset ℕ) (f : ℕ → ℕ → ℝ)
    (lo hi Q a : ℕ) : ℝ :=
  ∑ n ∈ (Ico lo hi).filter (fun n => Nat.ModEq Q n a),
    ∏ p ∈ P, (1 - scalarWeightedResidueLoss f p n)

theorem scalarWeightedResidue_elementary_error (P : Finset ℕ) (f : ℕ → ℕ → ℝ)
    (hP : ∀ p ∈ P, p.Prime) (hf : ∀ p ∈ P, ∀ r < p, 0 ≤ f p r)
    (k lo hi Q a : ℕ) (hlo : lo ≤ hi) (hQ : 0 < Q)
    (hcop : ∀ p ∈ P, p.Coprime Q) :
    |(∑ n ∈ scalarForcedResidueInterval lo hi Q a,
        elementarySum P (fun p => scalarWeightedResidueLoss f p n) k) -
      (((hi - lo : ℕ) : ℝ) / Q) * elementarySum P (scalarWeightedResidueMean f) k| ≤
      elementarySum P (scalarWeightedResidueMass f) k := by
  unfold elementarySum
  rw [sum_comm, mul_sum, ← sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro S hS
  have hsub := (mem_powersetCard.mp hS).1
  exact scalarWeightedResidue_monomial_error S f
    (fun p hp => hP p (hsub hp)) (fun p hp => hf p (hsub hp)) lo hi Q a hlo hQ
    (fun p hp => hcop p (hsub hp))

theorem scalarWeightedResidue_truncation_error (P : Finset ℕ) (f : ℕ → ℕ → ℝ)
    (hP : ∀ p ∈ P, p.Prime) (hf : ∀ p ∈ P, ∀ s < p, 0 ≤ f p s)
    (r lo hi Q a : ℕ) (hlo : lo ≤ hi) (hQ : 0 < Q)
    (hcop : ∀ p ∈ P, p.Coprime Q) :
    |scalarWeightedResidueTruncation P f r lo hi Q a -
      (((hi - lo : ℕ) : ℝ) / Q) * densityPolynomial r P (scalarWeightedResidueMean f)| ≤
      ∑ k ∈ range (r + 1), elementarySum P (scalarWeightedResidueMass f) k := by
  unfold scalarWeightedResidueTruncation densityPolynomial
  rw [sum_comm, mul_sum, ← sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro k _
  rw [← mul_sum]
  calc
    _ = |(-1 : ℝ) ^ k| *
        |(∑ n ∈ scalarForcedResidueInterval lo hi Q a,
            elementarySum P (fun p => scalarWeightedResidueLoss f p n) k) -
          (((hi - lo : ℕ) : ℝ) / Q) * elementarySum P (scalarWeightedResidueMean f) k| := by
      rw [← abs_mul]
      congr 1
      ring
    _ ≤ _ := by
      simpa using scalarWeightedResidue_elementary_error P f hP hf k lo hi Q a hlo hQ hcop

/-- The next layer and every retained coefficient are counted in the forced class.
The absolute remainder holds for every truncation order. -/
theorem scalarWeightedResidue_error (P : Finset ℕ) (f : ℕ → ℕ → ℝ)
    (hP : ∀ p ∈ P, p.Prime)
    (hf0 : ∀ p ∈ P, ∀ s < p, 0 ≤ f p s)
    (hf1 : ∀ p ∈ P, ∀ s < p, f p s ≤ 1)
    (r lo hi Q a : ℕ) (hlo : lo ≤ hi) (hQ : 0 < Q)
    (hcop : ∀ p ∈ P, p.Coprime Q) :
    let H := ((hi - lo : ℕ) : ℝ) / Q
    |scalarWeightedResidueCount P f lo hi Q a -
        H * ∏ p ∈ P, (1 - scalarWeightedResidueMean f p)| ≤
      2 * H * elementarySum P (scalarWeightedResidueMean f) (r + 1) +
        elementarySum P (scalarWeightedResidueMass f) (r + 1) +
        ∑ k ∈ range (r + 1), elementarySum P (scalarWeightedResidueMass f) k := by
  let H := ((hi - lo : ℕ) : ℝ) / Q
  let C := scalarWeightedResidueCount P f lo hi Q a
  let T := scalarWeightedResidueTruncation P f r lo hi Q a
  let A := H * densityPolynomial r P (scalarWeightedResidueMean f)
  let B := H * ∏ p ∈ P, (1 - scalarWeightedResidueMean f p)
  let E := elementarySum P (scalarWeightedResidueMean f) (r + 1)
  let F := elementarySum P (scalarWeightedResidueMass f) (r + 1)
  let G := ∑ k ∈ range (r + 1), elementarySum P (scalarWeightedResidueMass f) k
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hCT : |C - T| ≤ H * E + F := by
    have hpoint (n : ℕ) :
        |(∏ p ∈ P, (1 - scalarWeightedResidueLoss f p n)) -
          densityPolynomial r P (fun p => scalarWeightedResidueLoss f p n)| ≤
        elementarySum P (fun p => scalarWeightedResidueLoss f p n) (r + 1) := by
      rw [abs_sub_comm]
      exact scalarBonferroni_abs_error P _
        (fun p hp => hf0 p hp _ (Nat.mod_lt n (hP p hp).pos))
        (fun p hp => hf1 p hp _ (Nat.mod_lt n (hP p hp).pos)) r
    have he := scalarWeightedResidue_elementary_error P f hP hf0 (r + 1) lo hi Q a hlo hQ hcop
    change |C - T| ≤ _
    dsimp only [C, T, scalarWeightedResidueCount, scalarWeightedResidueTruncation]
    rw [← sum_sub_distrib]
    calc
      _ ≤ ∑ n ∈ scalarForcedResidueInterval lo hi Q a,
          elementarySum P (fun p => scalarWeightedResidueLoss f p n) (r + 1) :=
        (abs_sum_le_sum_abs _ _).trans (sum_le_sum (fun n _ => hpoint n))
      _ ≤ H * E + F := by
        have hh := (abs_le.mp he).2
        change _ ≤ F at hh
        linarith
  have hTA : |T - A| ≤ G :=
    scalarWeightedResidue_truncation_error P f hP hf0 r lo hi Q a hlo hQ hcop
  have hAB : |A - B| ≤ H * E := by
    dsimp only [A, B]
    rw [← mul_sub, abs_mul, abs_of_nonneg hH]
    exact mul_le_mul_of_nonneg_left (scalarBonferroni_abs_error P _
      (fun p hp => scalarWeightedResidueMean_nonneg f (hf0 p hp))
      (fun p hp => scalarWeightedResidueMean_le_one f (hP p hp).pos (hf1 p hp)) r) hH
  have htriangle₁ := abs_sub_le C T B
  have htriangle₂ := abs_sub_le T A B
  change |C - B| ≤ 2 * H * E + F + G
  linarith

theorem scalarWeightedResidue_error_by_layers (P : Finset ℕ) (f : ℕ → ℕ → ℝ)
    (hP : ∀ p ∈ P, p.Prime)
    (hf0 : ∀ p ∈ P, ∀ s < p, 0 ≤ f p s)
    (hf1 : ∀ p ∈ P, ∀ s < p, f p s ≤ 1)
    (r lo hi Q a : ℕ) (hlo : lo ≤ hi) (hQ : 0 < Q)
    (hcop : ∀ p ∈ P, p.Coprime Q) :
    let H := ((hi - lo : ℕ) : ℝ) / Q
    |scalarWeightedResidueCount P f lo hi Q a -
        H * ∏ p ∈ P, (1 - scalarWeightedResidueMean f p)| ≤
      2 * H * elementarySum P (scalarWeightedResidueMean f) (r + 1) +
        ∑ k ∈ range (r + 2), elementarySum P (scalarWeightedResidueMass f) k := by
  have hsum : (∑ k ∈ range (r + 2), elementarySum P (scalarWeightedResidueMass f) k) =
      elementarySum P (scalarWeightedResidueMass f) (r + 1) +
        ∑ k ∈ range (r + 1), elementarySum P (scalarWeightedResidueMass f) k := by
    rw [show r + 2 = (r + 1) + 1 by omega, sum_range_succ, add_comm]
  dsimp only
  rw [hsum]
  simpa only [add_assoc] using scalarWeightedResidue_error P f hP hf0 hf1
    r lo hi Q a hlo hQ hcop

theorem scalarWeightedResidueMean_factorial (P : Finset ℕ) (f : ℕ → ℕ → ℝ)
    (hf0 : ∀ p ∈ P, ∀ s < p, 0 ≤ f p s) (k : ℕ) :
    elementarySum P (scalarWeightedResidueMean f) k ≤
      (∑ p ∈ P, scalarWeightedResidueMean f p) ^ k / k.factorial := by
  have hnonneg := fun p hp => scalarWeightedResidueMean_nonneg f (hf0 p hp)
  exact elementarySum_le_pow_div_factorial P _ hnonneg (sum_nonneg hnonneg) le_rfl k

theorem scalarWeightedResidueEndpointMass_le (P : Finset ℕ) (f : ℕ → ℕ → ℝ)
    (hf0 : ∀ p ∈ P, ∀ s < p, 0 ≤ f p s)
    (h : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hmass : ∀ p ∈ P, scalarWeightedResidueMass f p ≤ B) :
    scalarWeightedResidueEndpointMass P f h ≤
      (h + 1 : ℝ) * (max 1 ((P.card : ℝ) * B)) ^ h := by
  have hnonneg := fun p hp => scalarWeightedResidueMass_nonneg f (hf0 p hp)
  have hsum : ∑ p ∈ P, scalarWeightedResidueMass f p ≤ (P.card : ℝ) * B := by
    calc
      _ ≤ ∑ _p ∈ P, B := sum_le_sum hmass
      _ = _ := by simp
  have hC : 0 ≤ (P.card : ℝ) * B := mul_nonneg (Nat.cast_nonneg _) hB
  unfold scalarWeightedResidueEndpointMass
  calc
    _ ≤ ∑ _k ∈ range (h + 1), (max 1 ((P.card : ℝ) * B)) ^ h := by
      apply sum_le_sum
      intro k hk
      calc
        _ ≤ ((P.card : ℝ) * B) ^ k / k.factorial :=
          elementarySum_le_pow_div_factorial P _ hnonneg hC hsum k
        _ ≤ ((P.card : ℝ) * B) ^ k :=
          div_le_self (pow_nonneg hC _)
            (by exact_mod_cast (show 1 ≤ k.factorial from Nat.factorial_pos k))
        _ ≤ (max 1 ((P.card : ℝ) * B)) ^ k :=
          pow_le_pow_left₀ hC (le_max_right _ _) k
        _ ≤ _ := pow_le_pow_right₀ (le_max_left _ _) (Nat.le_of_lt_succ (mem_range.mp hk))
    _ = _ := by simp

theorem scalarWeightedResidue_error_by_layers_Ico (P : Finset ℕ) (f : ℕ → ℕ → ℝ)
    (hP : ∀ p ∈ P, p.Prime)
    (hf0 : ∀ p ∈ P, ∀ s < p, 0 ≤ f p s)
    (hf1 : ∀ p ∈ P, ∀ s < p, f p s ≤ 1)
    (r lo hi Q a : ℕ) (hlo : lo ≤ hi) (hlo1 : 1 ≤ lo) (hQ : 0 < Q)
    (hcop : ∀ p ∈ P, p.Coprime Q) :
    let H := ((hi - lo : ℕ) : ℝ) / Q
    |scalarWeightedResidueCountIco P f lo hi Q a -
        H * ∏ p ∈ P, (1 - scalarWeightedResidueMean f p)| ≤
      2 * H * elementarySum P (scalarWeightedResidueMean f) (r + 1) +
        scalarWeightedResidueEndpointMass P f (r + 1) := by
  have hinterval : Ioc (lo - 1) (hi - 1) = Ico lo hi := by
    ext n
    simp only [mem_Ioc, mem_Ico]
    omega
  have hlen : hi - 1 - (lo - 1) = hi - lo := by omega
  have hcount : scalarWeightedResidueCount P f (lo - 1) (hi - 1) Q a =
      scalarWeightedResidueCountIco P f lo hi Q a := by
    simp only [scalarWeightedResidueCount, scalarWeightedResidueCountIco,
      scalarForcedResidueInterval, hinterval]
  simpa only [hcount, hlen, scalarWeightedResidueEndpointMass] using
    scalarWeightedResidue_error_by_layers P f hP hf0 hf1 r (lo - 1) (hi - 1) Q a
      (by omega) hQ hcop

end
end ArtinMatthews
