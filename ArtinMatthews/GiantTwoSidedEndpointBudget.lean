module

public import ArtinMatthews.GiantTwoSidedEndpointActual


set_option backward.privateInPublic true
@[expose] public section

/-! The endpoint estimates fit the literal transference budget, with an
exponent fixed before the active groups and list length. Position-only
multipliers of norm at most one preserve this estimate. -/
namespace ArtinMatthews
open Filter Finset
open scoped BigOperators ComplexConjugate
noncomputable section

theorem giantTwoSidedEndpointNorm_mono {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (M : ℕ) (Z : Finset ℕ) (q : ℝ) {F G : ℕ → ℂ}
    (hFG : ∀ n ∈ Z,‖F n‖ ≤ ‖G n‖) :
    giantTwoSidedEndpointNorm P M Z q F ≤ giantTwoSidedEndpointNorm P M Z q G := by
  have hV (i : J) : 0 ≤ bandReciprocalMass (P i) := sum_nonneg (fun _ _ => by positivity)
  unfold giantTwoSidedEndpointNorm giantTwoSidedEndpointEnergy
  apply Real.sqrt_le_sqrt
  apply sum_le_sum
  intro s _
  apply mul_le_mul_of_nonneg_left _ (markedPhysicalMass_nonneg _ M hV)
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  simp only [norm_mul]
  exact mul_le_mul_of_nonneg_left (hFG s.1.1.val s.1.1.property) (norm_nonneg _)

theorem giantTwoSidedEndpointNorm_mul_le {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (M : ℕ) (Z : Finset ℕ) (q : ℝ) (a F : ℕ → ℂ)
    (ha : ∀ n ∈ Z,‖a n‖ ≤ 1) :
    giantTwoSidedEndpointNorm P M Z q (fun n => a n*F n) ≤ giantTwoSidedEndpointNorm P M Z q F := by
  apply giantTwoSidedEndpointNorm_mono
  intro n hn
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (ha n hn)

theorem giantCandidateTwoSidedEndpointNorm_budget_eventually {J : Type*} [Fintype J]
    (e : J → ℝ) (he : ∀ i,0 < e i ∧ e i < 1)
    {ε : ℝ} (hε : 0 < ε) (hεq : ε < 1/4)
    {m : ℕ} (χ : DirichletCharacter ℂ m)
    {γ τ R q : ℝ} (hγ : 0 < γ) (hτ : 0 < τ) (hR : 1 ≤ R) (hq : q ∈ Set.Icc (0:ℝ) 1)
    (j : ℕ) (hj : 0 < j) :
    ∀ᶠ x : ℝ in atTop,∀ (S : Finset (GiantCandidateGroupIndex x)) (M : ℕ) (X : ℝ),
      1 ≤ X → X ≤ x^(1/τ) → ∀ Z : Finset ℕ,Z ⊆ Ioc 0 ⌊R*X⌋₊ →
      let P (i : S) := giantCandidateGroup x i.val
      let F (n : ℕ) := conj (giantCandidateFirstEndpoint e ε x n)
      let G (n : ℕ) := χ n*giantCandidateAllocationCore (giantCandidateFullPrimes x) (univ.biUnion P)
        (Real.exp ((Real.log x)^(6/25:ℝ))) (x^γ) j n
      let L := Real.log x
      let E := (((j*j:ℕ):ℝ)/2)+1
      (∀ n : ℕ,‖(giantTwoSidedEndpointDamping P M q n:ℂ)*F n‖ ≤ Real.exp (Real.sqrt L)) ∧
      giantTwoSidedEndpointNorm P M Z q F ≤ Real.sqrt X*L^E ∧
      giantTwoSidedEndpointNorm P M Z q G ≤ Real.sqrt X*L^E := by
  let C := (2/Real.log 2)^Fintype.card J
  let B := 1+Real.log (R+1)+1/τ
  let a := (((j*j:ℕ):ℝ)/2)
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hB : 0 ≤ B := add_nonneg
    (add_nonneg zero_le_one (Real.log_nonneg (by linarith))) (one_div_nonneg.mpr hτ.le)
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hs := (Real.tendsto_exp_atTop.comp (Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop)).eventually
    (eventually_ge_atTop C)
  filter_upwards [giantCandidateTwoSidedEndpointNorm_actual e he hε hεq χ hγ hτ hR hq j hj,
    hs,Real.tendsto_log_atTop.eventually_ge_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (C*Real.sqrt R),
    Real.tendsto_log_atTop.eventually_ge_atTop (Real.sqrt R*B^a)]
    with x h hsup hL hLC hLB
  intro S M X hX hXhi Z hZ
  let P (i : S) := giantCandidateGroup x i.val
  let F (n : ℕ) := conj (giantCandidateFirstEndpoint e ε x n)
  let G (n : ℕ) := χ n*giantCandidateAllocationCore (giantCandidateFullPrimes x) (univ.biUnion P)
    (Real.exp ((Real.log x)^(6/25:ℝ))) (x^γ) j n
  let L := Real.log x
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hLpow : L ≤ L^(a+1) := by
    calc
      L = L^(1:ℝ) := (Real.rpow_one L).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  have h' := h S M X hX hXhi Z hZ
  change (∀ n : ℕ,‖(giantTwoSidedEndpointDamping P M q n:ℂ)*F n‖ ≤ Real.exp (Real.sqrt L)) ∧
    giantTwoSidedEndpointNorm P M Z q F ≤ Real.sqrt X*L^(a+1) ∧
    giantTwoSidedEndpointNorm P M Z q G ≤ Real.sqrt X*L^(a+1)
  refine ⟨fun n => (h'.1 n).trans hsup,?_,?_⟩
  · calc
      _ ≤ C*Real.sqrt (R*X) := h'.2.1
      _ = (C*Real.sqrt R)*Real.sqrt X := by rw [Real.sqrt_mul hR0,mul_assoc]
      _ ≤ L*Real.sqrt X := mul_le_mul_of_nonneg_right hLC (Real.sqrt_nonneg _)
      _ ≤ _ := by rw [mul_comm L]; exact mul_le_mul_of_nonneg_left hLpow (Real.sqrt_nonneg _)
  · calc
      _ ≤ Real.sqrt (R*X)*(B*L)^a := h'.2.2
      _ = (Real.sqrt R*B^a)*(Real.sqrt X*L^a) := by
        rw [Real.sqrt_mul hR0,Real.mul_rpow hB hL0.le]
        ring
      _ ≤ L*(Real.sqrt X*L^a) := mul_le_mul_of_nonneg_right hLB (by positivity)
      _ = _ := by rw [Real.rpow_add hL0,Real.rpow_one]; ring

end
end ArtinMatthews
