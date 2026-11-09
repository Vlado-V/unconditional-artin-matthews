module

public import ArtinMatthews.GiantTwoSidedEndpointNorm
public import ArtinMatthews.GiantTwoSidedEndpointCore
public import ArtinMatthews.GiantCandidateSelectedGroups


set_option backward.privateInPublic true
@[expose] public section

/-! The two literal candidate correlation endpoints meet the physical
norm budget on any fixed enlargement of a positive dyad. The exponent
depends only on the fixed tuple length, with the original list mass
and both endpoint coefficients retained. -/
namespace ArtinMatthews
open Filter Finset
open scoped BigOperators ComplexConjugate
noncomputable section

theorem giantTwoSidedEndpoint_log_cap {x X R τ : ℝ} (hx : 1 < x)
    (hL : 1 ≤ Real.log x) (hR : 1 ≤ R) (hX : 1 ≤ X) (hXhi : X ≤ x^(1/τ)) :
    1+Real.log ((⌊R*X⌋₊:ℝ)+1) ≤ (1+Real.log (R+1)+1/τ)*Real.log x := by
  have hx0 := zero_lt_one.trans hx
  have hX0 := zero_lt_one.trans_le hX
  have hR0 := zero_lt_one.trans_le hR
  have hR1 : 0 < R+1 := by positivity
  have hN : (⌊R*X⌋₊:ℝ) ≤ R*X := Nat.floor_le (mul_nonneg hR0.le hX0.le)
  have harg : (⌊R*X⌋₊:ℝ)+1 ≤ (R+1)*X := by nlinarith
  have hlogX : Real.log X ≤ (1/τ)*Real.log x := by
    have h := Real.log_le_log hX0 hXhi
    rwa [Real.log_rpow hx0] at h
  have hlogN : Real.log ((⌊R*X⌋₊:ℝ)+1) ≤ Real.log (R+1)+(1/τ)*Real.log x := by
    calc
      _ ≤ Real.log ((R+1)*X) := Real.log_le_log (by positivity) harg
      _ = Real.log (R+1)+Real.log X := Real.log_mul hR1.ne' hX0.ne'
      _ ≤ _ := add_le_add le_rfl hlogX
  have hC : 0 ≤ 1+Real.log (R+1) := add_nonneg zero_le_one (Real.log_nonneg (by linarith))
  nlinarith only [hlogN,mul_le_mul_of_nonneg_left hL hC]

theorem giantCandidateTwoSidedEndpointNorm_actual {J : Type*} [Fintype J]
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
      (∀ n : ℕ,‖(giantTwoSidedEndpointDamping P M q n:ℂ)*F n‖ ≤ (2/Real.log 2)^Fintype.card J) ∧
      giantTwoSidedEndpointNorm P M Z q F ≤ (2/Real.log 2)^Fintype.card J*Real.sqrt (R*X) ∧
      giantTwoSidedEndpointNorm P M Z q G ≤ Real.sqrt (R*X) *
        ((1+Real.log (R+1)+1/τ)*Real.log x)^(((j*j:ℕ):ℝ)/2) := by
  filter_upwards [giantCandidateSelectedGroups_geometry_eventually,giantCandidateFullPrimes_prime_upper_eventually,
    giantCandidateFirstEndpoint_norm_eventually e he hε hεq,
    giantCandidateAllocationCore_character_actual_norm_le_stripped_fiber χ γ hγ j,
    eventually_gt_atTop (1:ℝ),Real.tendsto_log_atTop.eventually_ge_atTop (1:ℝ)]
    with x hgeo hprime hf hg hx hL
  intro S M X hX hXhi Z hZ
  let P (i : S) := giantCandidateGroup x i.val
  let F (n : ℕ) := conj (giantCandidateFirstEndpoint e ε x n)
  let G (n : ℕ) := χ n*giantCandidateAllocationCore (giantCandidateFullPrimes x) (univ.biUnion P)
    (Real.exp ((Real.log x)^(6/25:ℝ))) (x^γ) j n
  let C := (2/Real.log 2)^Fintype.card J
  let B := 1+Real.log (R+1)+1/τ
  let L := Real.log x
  let N := ⌊R*X⌋₊
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hlog : 0 < L := zero_lt_one.trans_le hL
  have hB : 0 ≤ B := add_nonneg
    (add_nonneg zero_le_one (Real.log_nonneg (by linarith))) (one_div_nonneg.mpr hτ.le)
  have hp : ∀ i p,p∈P i → p.Prime := by
    intro i p h
    exact (hprime p (mem_giantCandidateFullPrimes.mpr ⟨i.val,h⟩)).1
  have hV : ∀ i,0 < bandReciprocalMass (P i) :=
    fun i => (div_pos (Real.log_pos (by norm_num)) (by norm_num)).trans ((hgeo S).2.1 i).1
  have hf' (n : ℕ) : ‖F n‖ ≤ C := by
    simpa only [F,Complex.norm_conj] using hf n
  have hN : (N:ℝ) ≤ R*X := Nat.floor_le (mul_nonneg (zero_le_one.trans hR) (zero_le_one.trans hX))
  have hbase : 0 ≤ 1+Real.log ((N:ℝ)+1) :=
    add_nonneg zero_le_one (Real.log_nonneg (le_add_of_nonneg_left (Nat.cast_nonneg N)))
  have hcap : 1+Real.log ((N:ℝ)+1) ≤ B*L := giantTwoSidedEndpoint_log_cap hx hL hR hX hXhi
  have hroot : Real.sqrt ((B*L)^(j*j)) = (B*L)^(((j*j:ℕ):ℝ)/2) := by
    rw [Real.sqrt_eq_rpow,← Real.rpow_natCast,← Real.rpow_mul (mul_nonneg hB hlog.le)]
    congr 1
    ring
  change (∀ n : ℕ,‖(giantTwoSidedEndpointDamping P M q n:ℂ)*F n‖ ≤ C) ∧
    giantTwoSidedEndpointNorm P M Z q F ≤ C*Real.sqrt (R*X) ∧
    giantTwoSidedEndpointNorm P M Z q G ≤ Real.sqrt (R*X)*(B*L)^(((j*j:ℕ):ℝ)/2)
  refine ⟨fun n => (giantTwoSidedEndpoint_damped_norm_le P M hq F n).trans (hf' n),?_,?_⟩
  · exact (giantTwoSidedEndpointNorm_le_uniform P hp (hgeo S).1 hV M hZ hq F hC
      (fun n _ => hf' n)).trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hN) hC)
  · have hnorm := giantTwoSidedEndpointNorm_le_fiber P hp (hgeo S).1 hV M hZ hq G
      zero_le_one j hj (fun n _ => by simpa only [one_mul] using hg _ _ n)
    calc
      _ ≤ Real.sqrt (N:ℝ)*Real.sqrt ((1+Real.log ((N:ℝ)+1))^(j*j)) := by
        simpa only [one_mul] using hnorm
      _ ≤ Real.sqrt (R*X)*Real.sqrt ((B*L)^(j*j)) :=
        mul_le_mul (Real.sqrt_le_sqrt hN) (Real.sqrt_le_sqrt (pow_le_pow_left₀ hbase hcap _))
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = _ := by rw [hroot]

end
end ArtinMatthews
