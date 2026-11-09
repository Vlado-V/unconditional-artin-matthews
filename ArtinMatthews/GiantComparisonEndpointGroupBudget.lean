module

public import ArtinMatthews.GiantComparisonEndpointMarkMoment
public import ArtinMatthews.GiantCandidateSelectedGroups


set_option backward.privateInPublic true
@[expose] public section

/-! The cost from the variable number of selected groups is one fixed
logarithmic power for each fixed mark bound and moment. -/
namespace ArtinMatthews
open Filter Finset
open scoped BigOperators
noncomputable section

private theorem comparison_mark_factorial_le {G : Type*} [Fintype G]
    (P : G → Finset ℕ) (t : G → ℕ) (m : ℕ) {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hV : ∀ g, c ≤ bandReciprocalMass (P g)) (ht : ∀ g, t g ≤ m+1) :
    sourceComparisonMarkFactorialMass P t ≤
      (((m+1).factorial:ℝ)*(c⁻¹)^(m+1))^Fintype.card G := by
  let B := ((m+1).factorial:ℝ)*(c⁻¹)^(m+1)
  calc
    _ = ∏ g, ((t g).factorial:ℝ)/(bandReciprocalMass (P g))^t g := by
      rw [sourceComparisonMarkFactorialMass,sourceComparisonMarkMass,← prod_div_distrib]
    _ ≤ ∏ _g : G, B := by
      apply prod_le_prod₀ (fun g _ => div_nonneg (Nat.cast_nonneg _)
        (pow_nonneg (hc.le.trans (hV g)) _))
      intro g _
      unfold B
      rw [div_eq_mul_inv,← inv_pow]
      have hV0 := hc.trans_le (hV g)
      have hfinv : (bandReciprocalMass (P g))⁻¹ ≤ c⁻¹ := inv_anti₀ hc (hV g)
      have hcinv : 1 ≤ c⁻¹ := by simpa only [inv_one] using inv_anti₀ hc hc1
      exact mul_le_mul (Nat.cast_le.mpr (Nat.factorial_le (ht g)))
        ((pow_le_pow_left₀ (inv_nonneg.mpr hV0.le) hfinv _).trans
          (pow_le_pow_right₀ hcinv (ht g))) (by positivity) (Nat.cast_nonneg _)
    _ = _ := by simp [B]

private theorem comparison_mark_union_mass_le {G : Type*} [Fintype G]
    (P : G → Finset ℕ) (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    (hV : ∀ g, bandReciprocalMass (P g) ≤ 1) :
    (∑ p ∈ univ.biUnion P, 1/(p:ℝ)) ≤ (Fintype.card G:ℝ) := by
  classical
  rw [sum_biUnion (fun i _ j _ hij => hdis hij)]
  calc
    _ ≤ ∑ _g : G, (1:ℝ) := sum_le_sum (fun g _ => hV g)
    _ = _ := by simp

/-- Fixed cost of one selected group for a moment of order `k` with
at most `m+1` ordered marks in the group. -/
def giantComparisonEndpointGroupBase (m k : ℕ) : ℝ :=
  (((m+1).factorial:ℝ)*((Real.log 2/2)⁻¹)^(m+1))^k *
    Real.exp (Real.exp (2*(k:ℝ))-1)

theorem giantComparisonEndpointGroupBase_one_le (m k : ℕ) :
    1 ≤ giantComparisonEndpointGroupBase m k := by
  have hc : 0 < Real.log 2/2 := div_pos (Real.log_pos (by norm_num)) (by norm_num)
  have hc1 : Real.log 2/2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have hI : 1 ≤ (Real.log 2/2)⁻¹ := by simpa only [inv_one] using inv_anti₀ hc hc1
  have hf : 1 ≤ ((m+1).factorial:ℝ) := by exact_mod_cast Nat.factorial_pos (m+1)
  have hB : 1 ≤ Real.exp (2*(k:ℝ)) := Real.one_le_exp_iff.mpr (by positivity)
  unfold giantComparisonEndpointGroupBase
  exact one_le_mul_of_one_le_of_one_le (one_le_pow₀
    (one_le_mul_of_one_le_of_one_le hf (one_le_pow₀ hI)))
    (Real.one_le_exp_iff.mpr (sub_nonneg.mpr hB))

theorem giantCandidateComparisonMarkMomentBudget_eventually (m k : ℕ) :
    ∀ᶠ x : ℝ in atTop, ∀ (S : Finset (GiantCandidateGroupIndex x)) (t : S → ℕ),
      (∀ g, t g ≤ m+1) →
      let P (g : S) := giantCandidateGroup x g.val
      (sourceComparisonMarkFactorialMass P t)^k *
        Real.exp ((Real.exp (2*(k:ℝ))-1)*∑ p ∈ univ.biUnion P, 1/(p:ℝ)) ≤
          (Real.log x)^(giantCandidateGroupLogRate*Real.log (giantComparisonEndpointGroupBase m k)) := by
  let c : ℝ := Real.log 2/2
  let B : ℝ := ((m+1).factorial:ℝ)*(c⁻¹)^(m+1)
  let E : ℝ := Real.exp (2*(k:ℝ))-1
  have hc : 0 < c := div_pos (Real.log_pos (by norm_num)) (by norm_num)
  have hc1 : c ≤ 1 := by
    dsimp only [c]
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have hE : 0 ≤ E := sub_nonneg.mpr (Real.one_le_exp_iff.mpr (by positivity))
  filter_upwards [giantCandidateSelectedGroups_geometry_eventually,
    giantCandidateSelectedGroups_exponential_cost_eventually (giantComparisonEndpointGroupBase m k)
      (giantComparisonEndpointGroupBase_one_le m k)] with x hgeo hcost
  intro S t ht
  let P (g : S) := giantCandidateGroup x g.val
  have hV (g : S) : c < bandReciprocalMass (P g) := ((hgeo S).2.1 g).1
  have hA0 : 0 ≤ sourceComparisonMarkFactorialMass P t := by
    unfold sourceComparisonMarkFactorialMass
    exact div_nonneg (prod_nonneg fun _ _ => Nat.cast_nonneg _)
      (sourceComparisonMarkMass_pos P t (fun g => hc.trans (hV g))).le
  have hA : sourceComparisonMarkFactorialMass P t ≤ B^S.card := by
    simpa only [Fintype.card_coe] using comparison_mark_factorial_le P t m hc hc1
      (fun g => (hV g).le) ht
  have hm : (∑ p ∈ univ.biUnion P, 1/(p:ℝ)) ≤ (S.card:ℝ) := by
    simpa only [Fintype.card_coe] using comparison_mark_union_mass_le P (hgeo S).1
      (fun g => ((hgeo S).2.1 g).2.le)
  change (sourceComparisonMarkFactorialMass P t)^k *
      Real.exp (E*∑ p ∈ univ.biUnion P, 1/(p:ℝ)) ≤ _
  calc
    _ ≤ (B^S.card)^k*Real.exp (E*(S.card:ℝ)) :=
      mul_le_mul (pow_le_pow_left₀ hA0 hA _)
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hm hE))
        (Real.exp_pos _).le (by positivity)
    _ = (giantComparisonEndpointGroupBase m k)^S.card := by
      change (B^S.card)^k*Real.exp (E*(S.card:ℝ)) = (B^k*Real.exp E)^S.card
      have hpow : (B^S.card)^k = (B^k)^S.card := by
        rw [← pow_mul,← pow_mul,Nat.mul_comm S.card k]
      rw [hpow,mul_comm E,Real.exp_nat_mul,mul_pow (B^k) (Real.exp E)]
    _ ≤ _ := hcost S

end
end ArtinMatthews
