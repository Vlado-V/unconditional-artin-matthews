module

public import ArtinMatthews.GiantCandidateCoinMass
public import ArtinMatthews.GiantCandidateUnguardedCorrelation


set_option backward.privateInPublic true
@[expose] public section

/-! The original stripped proxy splits into retained and failed terms
without changing its ordered slots, fixed character, or product cutoff. -/
namespace ArtinMatthews
open Filter Finset
open scoped BigOperators
noncomputable section

def giantCandidateWeightedStrippedProxy {J : Type*} [Fintype J]
    (e : J → ℝ) {M : ℕ} (χ : DirichletCharacter ℂ M) (ε : ℝ) (Φ : ℝ → ℝ)
    (T γ : ℝ) (j : ℕ) (x : ℝ) (r : ℕ → ℝ) : ℂ :=
  (∑ t ∈ giantOrderedProductTuples j ⌊T*x⌋₊,
    let n := ∏ i,t i
    markedExtractionWeight e (giantMarkedCenteredCore ε) Φ x n *
      (∏ i, χ (t i) * giantCandidateStrippedSlotCoefficient (giantCandidateFullPrimes x)
        (Real.exp ((Real.log x)^(6/25:ℝ))) (x^γ) (t i)) * (r n:ℂ)) / j.factorial

def giantCandidateFailedProxyMass (x threshold c q T γ : ℝ) (j : ℕ) : ℝ :=
  (∑ t ∈ giantOrderedProductTuples j ⌊T*x⌋₊,
    giantCandidateFailedCoinMass x threshold c q j (∏ i,t i) *
      ∏ i, ‖giantCandidateStrippedSlotCoefficient (giantCandidateFullPrimes x)
        (Real.exp ((Real.log x)^(6/25:ℝ))) (x^γ) (t i)‖) / j.factorial

theorem giantCandidateStrippedProxy_partition {J : Type*} [Fintype J]
    (e : J → ℝ) {M : ℕ} (χ : DirichletCharacter ℂ M) (ε : ℝ) (Φ : ℝ → ℝ)
    (T γ : ℝ) (j : ℕ) (x threshold c q : ℝ) :
    giantOrdinaryStrippedProxyTupleSum giantCandidateFullPrimes e χ
      (giantMarkedCenteredCore ε) Φ T γ j x =
      giantCandidateWeightedStrippedProxy e χ ε Φ T γ j x
        (giantCandidateRetainedCoinMass x threshold c q j) +
      giantCandidateWeightedStrippedProxy e χ ε Φ T γ j x
        (giantCandidateFailedCoinMass x threshold c q j) := by
  unfold giantOrdinaryStrippedProxyTupleSum giantCandidateWeightedStrippedProxy
  rw [← add_div,← sum_add_distrib]
  apply congrArg (fun b : ℂ => b/(j.factorial:ℂ))
  apply sum_congr rfl
  intro t _
  rw [← mul_add,← Complex.ofReal_add,giantCandidateCoinMass_partition,Complex.ofReal_one,mul_one]

theorem giantCandidateFailedProxyError_bound {J : Type*} [Fintype J]
    (e : J → ℝ) (he : ∀ i,0 < e i ∧ e i < 1) {M : ℕ} (χ : DirichletCharacter ℂ M)
    {ε : ℝ} (hε : 0 < ε) (hεq : ε < 1/4) (Φ : ℝ → ℝ) (hΦ : Continuous Φ)
    {T : ℝ} (hT : 0 ≤ T) (γ : ℝ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (j : ℕ) (hj : 0 < j) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ x : ℝ in atTop, ∀ threshold : ℝ,
      let c := giantCandidateCoinScale q j
      ‖giantCandidateWeightedStrippedProxy e χ ε Φ T γ j x
        (giantCandidateFailedCoinMass x threshold c q j)‖ ≤
          D*giantCandidateFailedProxyMass x threshold c q T γ j := by
  have hG := (giantMarkedCenteredCore_interface e (fun i => (he i).2) hε hεq).mono
    (fun _ h => h.1)
  obtain ⟨D,hD,hW⟩ := markedExtractionWeight_bound e (fun i => (he i).1)
    (giantMarkedCenteredCore ε) zero_le_one hG Φ hΦ hT
  refine ⟨D,hD,?_⟩
  filter_upwards [hW,giantCandidateCoinMass_actual_bounds hq0 hq1 j hj,
    eventually_ge_atTop (0:ℝ)] with x hWx hcoin hx
  intro threshold
  let X := ⌊T*x⌋₊
  let c := giantCandidateCoinScale q j
  let r := giantCandidateFailedCoinMass x threshold c q j
  let a := giantCandidateStrippedSlotCoefficient (giantCandidateFullPrimes x)
    (Real.exp ((Real.log x)^(6/25:ℝ))) (x^γ)
  let F (t : Fin j → ℕ) : ℂ :=
    let n := ∏ i,t i
    markedExtractionWeight e (giantMarkedCenteredCore ε) Φ x n *
      (∏ i,χ (t i)*a (t i))*(r n:ℂ)
  change ‖(∑ t∈giantOrderedProductTuples j X,F t)/(j.factorial:ℂ)‖ ≤
    D*((∑ t∈giantOrderedProductTuples j X,r (∏ i,t i)*∏ i,‖a (t i)‖)/(j.factorial:ℝ))
  rw [norm_div,Complex.norm_natCast,← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg j.factorial)
  apply (norm_sum_le _ _).trans
  rw [Finset.mul_sum]
  apply sum_le_sum
  intro t ht
  let n := ∏ i,t i
  have hn : (n:ℝ) ≤ T*x :=
    (Nat.cast_le.mpr (mem_giantOrderedProductTuples.mp ht).2).trans (Nat.floor_le (mul_nonneg hT hx))
  have hr : 0 ≤ r n := (hcoin threshold n).2.1
  have hprod : ‖∏ i,χ (t i)*a (t i)‖ ≤ ∏ i,‖a (t i)‖ := by
    rw [norm_prod]
    apply prod_le_prod₀ (fun _ _ => norm_nonneg _)
    intro i _
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)
  change ‖markedExtractionWeight e (giantMarkedCenteredCore ε) Φ x n *
    (∏ i,χ (t i)*a (t i))*(r n:ℂ)‖ ≤ D*(r n*(∏ i,‖a (t i)‖))
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr]
  calc
    _ ≤ D*(∏ i,‖a (t i)‖)*r n := mul_le_mul_of_nonneg_right
      (mul_le_mul (hWx n hn) hprod (norm_nonneg _) hD) hr
    _ = _ := by ring

end
end ArtinMatthews
