module

public import ArtinMatthews.GiantCandidateTupleDyads
public import ArtinMatthews.GiantCandidateDyadActual
public import ArtinMatthews.GiantCandidateDyadBudget
public import ArtinMatthews.PrimeExtractionWeightUniform


set_option backward.privateInPublic true
@[expose] public section

/-! Absolute error for the candidate prime-power removal in the
original rough proxy. The product cutoff and all outer weights remain
at the original tuple product. -/

namespace ArtinMatthews
noncomputable section
open Finset Filter
open scoped Asymptotics BigOperators

theorem giant_ordinary_proxy_sub_stripped_isBigO {J : Type*} [Fintype J]
    (P : ℝ → Finset ℕ)
    (hP : ∀ᶠ x : ℝ in atTop,∀ p∈P x,p.Prime ∧
      (p:ℝ)≤Real.exp ((Real.log x)^(9/20:ℝ)))
    (e : J → ℝ) (he : ∀ i,0 < e i) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (G : ℝ → ℕ → ℂ) {M : ℝ} (hM : 0 ≤ M)
    (hG : ∀ᶠ x : ℝ in atTop,∀ n,‖G x n‖ ≤ M)
    (Φ : ℝ → ℝ) (hΦ : Continuous Φ) {T γ : ℝ}
    (hT : 0 < T) (hγ : 0 < γ) (j : ℕ) (hj : 2 ≤ j) :
    (fun x => giantOrdinaryProxyTupleSum e χ G Φ T γ j x -
      giantOrdinaryStrippedProxyTupleSum P e χ G Φ T γ j x) =O[atTop]
        (fun x : ℝ => x*(Real.log x)^(-(1/10:ℝ))/Real.log x) := by
  obtain ⟨C,hC,hweight⟩ := markedExtractionWeight_bound e he G hM hG Φ hΦ hT.le
  let A := 1+2/Real.log 2
  let B := 2+1/Real.log 2
  let U := 4/γ
  let D := giantCandidateRegularErrorConstant γ
  let E := 8/γ
  let R := 2*T*U^(j-1)*(D*A^(j-1)+E*B*A^(j-2))
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hD : 0 ≤ D := giantCandidateRegularErrorConstant_nonneg hγ
  have hE : 0 ≤ E := by dsimp [E]; positivity
  apply Asymptotics.IsBigO.of_bound (C*(j:ℝ)*R)
  filter_upwards [hweight,giant_candidate_slot_dyad_rows_eventually γ hγ P hP,
    eventually_gt_atTop (1:ℝ),eventually_ge_atTop (T⁻¹),
    Real.tendsto_log_atTop.eventually_ge_atTop (max 1 (Real.log (T+1)))]
    with x hw hrows hx hxT hlog
  let L := Real.log x
  let W := Real.exp (L^(6/25:ℝ))
  let z := x^γ
  let N := ⌊T*x⌋₊
  let K := ((Nat.log 2 N+1:ℕ):ℝ)
  let I := giantCandidateThresholdDyadIndices (γ*L) (L^(9/10:ℝ))
  let u := giantCandidateProxyEnvelope W z
  let d (m : ℕ) := ‖giantRoughSlotCoefficient W z m -
    giantCandidateStrippedSlotCoefficient (P x) W z m‖
  have hx₀ := zero_lt_one.trans hx
  have hL₁ : 1 ≤ L := (le_max_left _ _).trans hlog
  have hL : 0 < L := zero_lt_one.trans_le hL₁
  have hTlog : Real.log (T+1) ≤ L := (le_max_right _ _).trans hlog
  have hz : 1 < z := Real.one_lt_rpow hx hγ
  have hNbound : (N:ℝ) ≤ T*x := Nat.floor_le (mul_pos hT hx₀).le
  have hN : 0 < N := by
    apply Nat.le_floor
    simpa only [Nat.cast_one,mul_inv_cancel₀ hT.ne'] using mul_le_mul_of_nonneg_left hxT hT.le
  have hKbound : K ≤ A*L := (primeExtractionDyadicIndex_count_le N).trans
    (primeExtractionDyadicLogGrowth hT.le hx.le hTlog hL₁ hNbound)
  have hIbound : (I.card:ℝ) ≤ B*L^(9/10:ℝ) := giantCandidateThresholdDyad_card_actual_le hγ.le hL₁
  have hmass (i : Fin j) : giantCandidatePositiveTupleMass N i d u ≤ R*(x*L^(-(1/10:ℝ))/L) := by
    have h₁ := giantCandidatePositiveTupleMass_le_rows hj N hN i d u
      (fun _ => norm_nonneg _) (giantCandidateProxyEnvelope_nonneg hz)
      (U/L) (D*L^(-(1/10:ℝ))/L) (E/L)
      (div_nonneg hU hL.le) (div_nonneg (mul_nonneg hD (Real.rpow_nonneg hL.le _)) hL.le)
      (div_nonneg hE hL.le) I (fun k => (hrows N k).1) (fun k => (hrows N k).2)
    exact h₁.trans (giantCandidateDyadLogBudget j hj hL (Nat.cast_nonneg N)
      (Nat.cast_nonneg (Nat.log 2 N+1)) (Nat.cast_nonneg I.card) hU hD hE hNbound hKbound hIbound)
  have herr := giant_ordinary_proxy_sub_stripped_norm_le P e χ G Φ T γ j x C hC hz
    (fun n hn => hw n ((Nat.cast_le.mpr hn).trans hNbound))
  change ‖giantOrdinaryProxyTupleSum e χ G Φ T γ j x -
    giantOrdinaryStrippedProxyTupleSum P e χ G Φ T γ j x‖ ≤
      (C*(j:ℝ)*R)*‖x*L^(-(1/10:ℝ))/L‖
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ x*L^(-(1/10:ℝ))/L)]
  calc
    _ ≤ C*∑ i : Fin j,giantCandidatePositiveTupleMass N i d u := herr
    _ ≤ C*∑ _i : Fin j,R*(x*L^(-(1/10:ℝ))/L) :=
      mul_le_mul_of_nonneg_left (sum_le_sum (fun i _ => hmass i)) hC
    _ = _ := by
      rw [sum_const,nsmul_eq_mul,card_univ,Fintype.card_fin]
      ring

theorem giant_ordinary_proxy_sub_stripped_isLittleO {J : Type*} [Fintype J]
    (P : ℝ → Finset ℕ)
    (hP : ∀ᶠ x : ℝ in atTop,∀ p∈P x,p.Prime ∧
      (p:ℝ)≤Real.exp ((Real.log x)^(9/20:ℝ)))
    (e : J → ℝ) (he : ∀ i,0 < e i) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (G : ℝ → ℕ → ℂ) {M : ℝ} (hM : 0 ≤ M)
    (hG : ∀ᶠ x : ℝ in atTop,∀ n,‖G x n‖ ≤ M)
    (Φ : ℝ → ℝ) (hΦ : Continuous Φ) {T γ : ℝ}
    (hT : 0 < T) (hγ : 0 < γ) (j : ℕ) (hj : 2 ≤ j) :
    (fun x => giantOrdinaryProxyTupleSum e χ G Φ T γ j x -
      giantOrdinaryStrippedProxyTupleSum P e χ G Φ T γ j x) =o[atTop]
        (fun x : ℝ => x/Real.log x) :=
  (giant_ordinary_proxy_sub_stripped_isBigO P hP e he χ G hM hG Φ hΦ hT hγ j hj).trans_isLittleO
    giantCandidateLogTenth_isLittleO

end
end ArtinMatthews
