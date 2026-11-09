module

public import ArtinMatthews.GiantCandidateDyadRows


set_option backward.privateInPublic true
@[expose] public section

/-! The actual dyadic row bounds at W = exp(log(x)^.24) and z = x^γ.
Both the large-removal and reciprocal-log contributions have a uniform
extra logarithmic saving. -/

namespace ArtinMatthews
noncomputable section
open Finset Filter
open scoped BigOperators

def giantCandidateRegularErrorConstant (γ : ℝ) : ℝ :=
  16*Real.exp (Real.eulerMascheroniConstant+1)/γ+4/γ^2

theorem giantCandidateRegularErrorConstant_nonneg {γ : ℝ} (hγ : 0 < γ) :
    0 ≤ giantCandidateRegularErrorConstant γ := by
  unfold giantCandidateRegularErrorConstant
  positivity

theorem giant_candidate_slot_dyad_rows_eventually (γ : ℝ) (hγ : 0 < γ)
    (P : ℝ → Finset ℕ)
    (hP : ∀ᶠ x : ℝ in atTop, ∀ p ∈ P x,
      p.Prime ∧ (p:ℝ) ≤ Real.exp ((Real.log x)^(9/20:ℝ))) :
    ∀ᶠ x : ℝ in atTop, ∀ N k : ℕ,
      let L := Real.log x
      let W := Real.exp (L^(6/25:ℝ))
      let z := x^γ
      let I := giantCandidateThresholdDyadIndices (γ*L) (L^(9/10:ℝ))
      ((∑ m ∈ primeExtractionDyadicBlock N k,giantCandidateProxyEnvelope W z m) ≤
        ((4/γ)/L)*(2:ℝ)^k) ∧
      ((∑ m ∈ primeExtractionDyadicBlock N k,
        ‖giantRoughSlotCoefficient W z m-giantCandidateStrippedSlotCoefficient (P x) W z m‖) ≤
        (giantCandidateRegularErrorConstant γ*L^(-(1/10:ℝ))/L +
          (if k ∈ I then (8/γ)/L else 0))*(2:ℝ)^k) := by
  let E := Real.exp (Real.eulerMascheroniConstant+1)
  filter_upwards [giant_candidate_rough_dyad_card_eventually γ hγ,
    Real.tendsto_log_atTop.eventually (marked_rough_density_inverse_cutoff (6/25) (by norm_num)),
    hP,eventually_gt_atTop (1:ℝ),Real.tendsto_log_atTop.eventually_ge_atTop (1:ℝ)]
    with x hrough hVinv hPx hx hL₁
  intro N k
  let L := Real.log x
  let W := Real.exp (L^(6/25:ℝ))
  let z := x^γ
  let V := markedSieveEulerProduct W
  let A := giantCandidateSlotBound W z
  let R := L^(9/10:ℝ)
  let H := (2:ℝ)^k
  let I := giantCandidateThresholdDyadIndices (γ*L) R
  have hL : 0 < L := zero_lt_one.trans_le hL₁
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hz : 1 < z := Real.one_lt_rpow hx hγ
  have hV : 0 < V := markedSieveEulerProduct_pos W
  have hlogz : Real.log z = γ*L := by
    exact Real.log_rpow (zero_lt_one.trans hx) γ
  have hA : 0 ≤ A := giantCandidateSlotBound_nonneg hz
  have hAeq : A = V⁻¹/(γ*L) := by
    change (markedSieveEulerProduct W)⁻¹/Real.log z = _
    rw [hlogz]
  have hAV : A*V = 1/(γ*L) := by
    rw [hAeq]
    field_simp [hV.ne',hγ.ne',hL.ne']
  have hrough' : ((giantCandidateRoughDyad W z N k).card:ℝ) ≤ 4*H*V := hrough N k
  constructor
  · change (∑ m ∈ primeExtractionDyadicBlock N k,giantCandidateProxyEnvelope W z m) ≤ ((4/γ)/L)*H
    rw [giantCandidateEnvelope_dyad_sum]
    calc
      _ ≤ (4*H*V)*A := mul_le_mul_of_nonneg_right hrough' hA
      _ = (4*H)*(A*V) := by ring
      _ = _ := by rw [hAV]; ring
  · have hD := giantCandidateDifference_dyad_sum_le (P x) (fun p hp => (hPx p hp).1)
      (W:=W) hz hL (fun p hp => (hPx p hp).2) N k hrough'
    change _ ≤ 2*A*(8*H*L^(-(9/20:ℝ)))+
      2*A*(if k ∈ giantCandidateThresholdDyadIndices (Real.log z) R then 4*H*V else 0)+
        (A*R/Real.log z)*(4*H*V) at hD
    rw [hlogz] at hD
    change (∑ m ∈ primeExtractionDyadicBlock N k,
      ‖giantRoughSlotCoefficient W z m-giantCandidateStrippedSlotCoefficient (P x) W z m‖) ≤
      (giantCandidateRegularErrorConstant γ*L^(-(1/10:ℝ))/L+(if k ∈ I then (8/γ)/L else 0))*H
    have hbig : 16*A*L^(-(9/20:ℝ)) ≤ (16*E/γ)*L^(-(1/10:ℝ))/L := by
      have hVinv' : V⁻¹ ≤ E*L^(6/25:ℝ) := hVinv
      have hpow : L^(6/25:ℝ)*L^(-(9/20:ℝ)) ≤ L^(-(1/10:ℝ)) := by
        rw [← Real.rpow_add hL]
        exact Real.rpow_le_rpow_of_exponent_le hL₁ (by norm_num)
      rw [hAeq]
      calc
        _ ≤ 16*(E*L^(6/25:ℝ)/(γ*L))*L^(-(9/20:ℝ)) := by
          gcongr
        _ = (16*E/γ)*(L^(6/25:ℝ)*L^(-(9/20:ℝ)))/L := by ring
        _ ≤ _ := by
          apply div_le_div_of_nonneg_right _ hL.le
          exact mul_le_mul_of_nonneg_left hpow (by positivity)
    have hsmall : 4*(A*V)*(R/(γ*L)) = (4/γ^2)*L^(-(1/10:ℝ))/L := by
      have hratio : R/L = L^(-(1/10:ℝ)) := by
        calc
          _ = R/L^(1:ℝ) := by rw [Real.rpow_one]
          _ = _ := by
            change L^(9/10:ℝ)/L^(1:ℝ) = _
            rw [← Real.rpow_sub hL]
            norm_num
      rw [hAV,← hratio]
      ring
    have hstrip : (if k ∈ I then 8*(A*V) else 0) =
        if k ∈ I then (8/γ)/L else 0 := by
      rw [hAV]
      split_ifs <;> ring
    calc
      _ ≤ 2*A*(8*H*L^(-(9/20:ℝ)))+
        2*A*(if k ∈ I then 4*H*V else 0)+(A*R/(γ*L))*(4*H*V) := hD
      _ = (16*A*L^(-(9/20:ℝ))+(if k ∈ I then 8*(A*V) else 0)+
          4*(A*V)*(R/(γ*L)))*H := by split_ifs <;> ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ hH
        rw [hsmall,hstrip]
        change _ ≤ (16*E/γ+4/γ^2)*L^(-(1/10:ℝ))/L+(if k∈I then (8/γ)/L else 0)
        rw [add_mul,add_div]
        linarith only [hbig]

end
end ArtinMatthews
