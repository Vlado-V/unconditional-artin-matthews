module

public import ArtinMatthews.GiantCandidateSquareDecay
public import ArtinMatthews.GiantCandidateSquareGuards
public import ArtinMatthews.GiantCandidateSquareCore
public import ArtinMatthews.GiantCandidateOneMarkBounds
public import ArtinMatthews.GiantCandidateAllocationTuple


set_option backward.privateInPublic true
@[expose] public section

/-! Before allocation, inserting the literal full-candidate square guard
into an expanded one-mark term costs every fixed logarithmic power. -/
namespace ArtinMatthews
open Finset Filter
open scoped BigOperators
noncomputable section

def giantCandidateActualUnguardedMarkedProxyTerm {J ι : Type*} [Fintype J] [Fintype ι]
    (C : Finset ℕ) (P : ι → Finset ℕ) (e : J → ℝ) {M : ℕ} (χ : DirichletCharacter ℂ M)
    (ε : ℝ) (Φ : ℝ → ℝ) (T γ q : ℝ) (j : ℕ) (x : ℝ) : ℂ :=
  (∑ t ∈ giantOrderedProductTuples j ⌊T*x⌋₊,
      let n := ∏ i, t i
      markedExtractionWeight e (giantMarkedCenteredCore ε) Φ x n *
        (giantCandidateActiveOneMark P q (n-1) : ℂ) *
        ((∏ i, χ (t i) * giantCandidateStrippedSlotCoefficient C
          (Real.exp ((Real.log x)^(6/25:ℝ))) (x^γ) (t i)) *
            (giantCandidateActiveOneMark P (q/(j:ℝ)) n : ℂ))) / j.factorial

theorem giantCandidateActualMarkedProxyTerm_square_guard_log_saving {J : Type*} [Fintype J]
    (e : J → ℝ) (he : ∀ i, 0 < e i ∧ e i < 1) {M : ℕ} (χ : DirichletCharacter ℂ M)
    {ε : ℝ} (hε : 0 < ε) (hεq : ε < 1/4) (Φ : ℝ → ℝ) (hΦ : Continuous Φ)
    {T γ q : ℝ} (hT : 0 ≤ T) (hγ : 0 < γ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (j : ℕ) (hj : 0 < j) (A : ℝ) :
    ∀ᶠ x : ℝ in atTop,∀ S : Finset (GiantCandidateGroupIndex x),
      let P (i : S) := giantCandidateGroup x i.val
      let C := giantCandidateFullPrimes x
      ‖giantCandidateActualUnguardedMarkedProxyTerm C P e χ ε Φ T γ q j x -
        giantCandidateActualMarkedProxyTerm C P e χ ε Φ T γ q j x‖ ≤
          x*(Real.log x)^(-A) := by
  have hG := (giantMarkedCenteredCore_interface e (fun i => (he i).2) hε hεq).mono
    (fun _ h => h.1)
  obtain ⟨D,hD,hW⟩ := markedExtractionWeight_bound e (fun i => (he i).1)
    (giantMarkedCenteredCore ε) zero_le_one hG Φ hΦ hT
  have hj1 : (1:ℝ) ≤ j := Nat.one_le_cast.mpr hj
  have hqj0 : 0 ≤ q/(j:ℝ) := div_nonneg hq0 (Nat.cast_nonneg _)
  have hqj1 : q/(j:ℝ) < 1 := (div_le_self hq0 hj1).trans_lt hq1
  let c := giantCandidateGroupLogRate*Real.log (giantCandidateOneMarkBound q)
  let c' := giantCandidateGroupLogRate*Real.log (giantCandidateOneMarkBound (q/(j:ℝ)))
  filter_upwards [hW,giantCandidateStrippedSlotCoefficient_actual_norm_le_one γ hγ,
    giantCandidateActiveOneMark_actual_bound hq0 hq1,
    giantCandidateActiveOneMark_actual_bound hqj0 hqj1,
    giantCandidateSquareFiberMass_log_saving j T D (c+c') A hT hD,
    eventually_ge_atTop (0:ℝ),eventually_gt_atTop (1:ℝ)] with x hWx hslot hmark hmark' hmass hx hx1
  intro S
  let C := giantCandidateFullPrimes x
  let P (i : S) := giantCandidateGroup x i.val
  let X := ⌊T*x⌋₊
  let L := Real.log x
  let a := giantCandidateStrippedSlotCoefficient C (Real.exp (L^(6/25:ℝ))) (x^γ)
  let F (t : Fin j → ℕ) : ℂ :=
    let n := ∏ i,t i
    markedExtractionWeight e (giantMarkedCenteredCore ε) Φ x n *
      (giantCandidateActiveOneMark P q (n-1):ℂ) *
        ((∏ i,χ (t i)*a (t i)) * (giantCandidateActiveOneMark P (q/(j:ℝ)) n:ℂ))
  have hX : (X:ℝ) ≤ T*x := Nat.floor_le (mul_nonneg hT hx)
  have hL : 0 < L := Real.log_pos hx1
  have hprod (t : Fin j → ℕ) : ‖∏ i,χ (t i)*a (t i)‖ ≤ 1 := by
    rw [norm_prod]
    apply prod_le_one₀ (fun _ _ => norm_nonneg _)
    intro i _
    rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (hslot C (t i))).trans (χ.norm_le_one _)
  have hF (t : Fin j → ℕ) (ht : t ∈ giantOrderedProductTuples j X) : ‖F t‖ ≤ D*L^(c+c') := by
    let n := ∏ i,t i
    have hn : (n:ℝ) ≤ T*x :=
      (Nat.cast_le.mpr (mem_giantOrderedProductTuples.mp ht).2).trans hX
    change ‖markedExtractionWeight e (giantMarkedCenteredCore ε) Φ x n *
      (giantCandidateActiveOneMark P q (n-1):ℂ) *
        ((∏ i,χ (t i)*a (t i)) * (giantCandidateActiveOneMark P (q/(j:ℝ)) n:ℂ))‖ ≤ _
    simp only [norm_mul]
    calc
      _ ≤ (D*L^c)*(1*L^c') := mul_le_mul
        (mul_le_mul (hWx n hn) (hmark S (n-1)) (norm_nonneg _) hD)
        (mul_le_mul (hprod t) (hmark' S n) (norm_nonneg _) zero_le_one)
        (by positivity) (mul_nonneg hD (Real.rpow_nonneg hL.le _))
      _ = _ := by rw [one_mul,mul_assoc,← Real.rpow_add hL]
  have hfac : (1:ℝ) ≤ ‖(j.factorial:ℂ)‖ := by
    rw [Complex.norm_natCast]
    exact Nat.one_le_cast.mpr (Nat.factorial_pos j)
  change ‖(∑ t ∈ giantOrderedProductTuples j X,F t)/(j.factorial:ℂ) -
    (∑ t ∈ (giantOrderedProductTuples j X).filter (fun t => ∀ p ∈ C,¬p^2 ∣ ∏ i,t i),F t)/
      (j.factorial:ℂ)‖ ≤ _
  rw [← sub_div,norm_div]
  exact (div_le_self (norm_nonneg _) hfac).trans
    ((giantCandidateSquareTuples_guard_error_le C X j F hF).trans (hmass X hX))

end
end ArtinMatthews
