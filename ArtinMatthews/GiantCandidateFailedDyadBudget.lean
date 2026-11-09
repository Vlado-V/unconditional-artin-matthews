module

public import ArtinMatthews.GiantCandidateFailedDyadReindex
public import ArtinMatthews.GiantCandidateFailedDyadCard
public import ArtinMatthews.PrimeExtractionDyadicLogGrowth
public import ArtinMatthews.PrimeExtractionRelevantGeometry


set_option backward.privateInPublic true
@[expose] public section

/-! The literal full-dyad expectation controls the positive failed tuple
mass at the original x/log x scale. The actual rough counts cancel the
reciprocal sieve factors in the slot envelope. -/
namespace ArtinMatthews
open Filter Finset
open scoped BigOperators
noncomputable section

theorem giantCandidateFailedProxyMass_bound_of_dyad_mean {T γ q : ℝ}
    (hT : 0 < T) (hγ : 0 < γ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (j : ℕ) (hj : 0 < j) :
    ∃ D : ℝ,0 < D ∧ ∀ᶠ x : ℝ in atTop,∀ threshold δ : ℝ,0 ≤ δ →
      let c := giantCandidateCoinScale q j
      (∀ H : Fin j → ℕ,(∀ i,x^(γ/2) ≤ (H i:ℝ)) →
        giantCandidateFailedBoxMean x threshold c q H ≤ δ) →
      giantCandidateFailedProxyMass x threshold c q T γ j ≤ D*δ*(x/Real.log x) := by
  let B := 1+2/Real.log 2
  let D := 2*T*(2/γ)^j*B^(j-1)/(j.factorial:ℝ)
  have hD : 0 < D := by dsimp only [D,B]; positivity
  refine ⟨D,hD,?_⟩
  filter_upwards [giantCandidateFullRoughBox_card_eventually (half_pos hγ) j,
    giantCandidateCoinMass_actual_bounds hq0 hq1 j hj,prime_extraction_half_power_le_eventually hγ,
    eventually_gt_atTop (1:ℝ),eventually_ge_atTop T⁻¹,
    Real.tendsto_log_atTop.eventually_ge_atTop (max 1 (Real.log (T+1)))]
    with x hbox hcoin hhalf hx hxT hlog
  intro threshold δ hδ c hmean
  let N := ⌊T*x⌋₊
  let L := Real.log x
  let W := Real.exp (L^(6/25:ℝ))
  let V := markedSieveEulerProduct W
  let A := giantCandidateSlotBound W (x^γ)
  let H (key : Fin j → ℕ) (i : Fin j) := (2:ℕ)^key i
  let S := giantProxyDyadKeys j N
  let K := S.filter (fun key => ∀ i,x^(γ/2) ≤ (H key i:ℝ))
  let M (key : Fin j → ℕ) := giantCandidateFailedBoxMean x threshold c q (H key)
  let R (key : Fin j → ℕ) : ℝ := (giantCandidateFullRoughBox x (H key)).card
  let Y := ((Nat.log 2 N+1:ℕ):ℝ)
  have hx0 := zero_lt_one.trans hx
  have hL : 0 < L := Real.log_pos hx
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hlog
  have hlogT : Real.log (T+1) ≤ L := (le_max_right _ _).trans hlog
  have hz : 1 < x^γ := Real.one_lt_rpow hx hγ
  have hV : 0 < V := markedSieveEulerProduct_pos W
  have hA : 0 ≤ A := giantCandidateSlotBound_nonneg hz
  have hNbound : (N:ℝ) ≤ T*x := Nat.floor_le (mul_nonneg hT.le hx0.le)
  have hN : 0 < N := by
    apply Nat.le_floor
    simpa only [Nat.cast_one,mul_inv_cancel₀ hT.ne'] using mul_le_mul_of_nonneg_left hxT hT.le
  have hY : Y ≤ B*L := (primeExtractionDyadicIndex_count_le N).trans
    (primeExtractionDyadicLogGrowth hT.le hx.le hlogT hL1 hNbound)
  have hAV : A*(2*V)=2/(γ*L) := by
    change V⁻¹/Real.log (x^γ)*(2*V) = _
    rw [Real.log_rpow hx0]
    change V⁻¹/(γ*L)*(2*V) = 2/(γ*L)
    field_simp [hV.ne',hγ.ne',hL.ne']
  have hcard (key : Fin j → ℕ) (hk : key ∈ K) :
      R key ≤ (2*V)^j*giantProxyDyadKeyWeight key := by
    have hh := (mem_filter.mp hk).2
    have h := (hbox (H key) hh).2
    rw [giantProxyDyadKeyWeight_eq_prod]
    simpa only [H,Nat.cast_pow,Nat.cast_ofNat] using h
  have hsum : (∑ key ∈ K,M key*R key) ≤
      δ*(2*V)^j*(2*(N:ℝ)*Y^(j-1)) := by
    have hsub : K ⊆ S := filter_subset _ _
    calc
      _ ≤ ∑ key ∈ K,δ*((2*V)^j*giantProxyDyadKeyWeight key) := by
        apply sum_le_sum
        intro key hk
        exact mul_le_mul (hmean (H key) (mem_filter.mp hk).2) (hcard key hk) (Nat.cast_nonneg _) hδ
      _ = δ*(2*V)^j*∑ key ∈ K,giantProxyDyadKeyWeight key := by simp only [Finset.mul_sum,mul_assoc]
      _ ≤ δ*(2*V)^j*∑ key ∈ S,giantProxyDyadKeyWeight key :=
        mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.cast_nonneg _))
          (mul_nonneg hδ (pow_nonneg (mul_nonneg (by norm_num) hV.le) j))
      _ ≤ _ := mul_le_mul_of_nonneg_left (giantProxyDyadKeys_weight_sum_le j N hj hN)
        (mul_nonneg hδ (pow_nonneg (mul_nonneg (by norm_num) hV.le) j))
  have hDpow : L^j = L^(j-1)*L := by
    rw [← pow_succ,show j-1+1=j by omega]
  change giantCandidateFailedProxyMass x threshold c q T γ j ≤ D*δ*(x/L)
  calc
    _ ≤ (A^j*(∑ key ∈ K,M key*R key))/(j.factorial:ℝ) :=
      giantCandidateFailedProxyMass_le_dyad_means x threshold c q T γ j hz hhalf
        (fun v => (hcoin threshold v).2.1)
    _ ≤ (A^j*(δ*(2*V)^j*(2*(N:ℝ)*Y^(j-1))))/(j.factorial:ℝ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsum (pow_nonneg hA j)) (Nat.cast_nonneg _)
    _ ≤ (A^j*(δ*(2*V)^j*(2*(T*x)*(B*L)^(j-1))))/(j.factorial:ℝ) := by gcongr
    _ = ((A*(2*V))^j*(δ*(2*(T*x)*(B*L)^(j-1))))/(j.factorial:ℝ) := by rw [mul_pow]; ring
    _ = _ := by
      rw [hAV]
      unfold D
      rw [show 2/(γ*L)=(2/γ)/L by rw [div_div]]
      simp only [div_pow,mul_pow]
      rw [hDpow]
      field_simp [hL.ne',pow_ne_zero _ hL.ne',Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)]

end
end ArtinMatthews
