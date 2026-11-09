module

public import ArtinMatthews.GiantCandidateSquareDecay
public import ArtinMatthews.GiantCandidateSquareGuards
public import ArtinMatthews.GiantCandidateSquareCore
public import ArtinMatthews.GiantCandidateOneMarkBounds
public import ArtinMatthews.GiantCandidateAllocationTuple


set_option backward.privateInPublic true
@[expose] public section

/-! After allocation, restoring the same square exceptions preserves the
literal character, stripped core, damping, and ordered slot factorial. -/
namespace ArtinMatthews
open Finset Filter
open scoped BigOperators
noncomputable section

def giantCandidateActualUnguardedAllocatedTerm {J ι : Type*} [Fintype J] [Fintype ι]
    (C : Finset ℕ) (P : ι → Finset ℕ) (e : J → ℝ) {M : ℕ} (χ : DirichletCharacter ℂ M)
    (ε : ℝ) (Φ : ℝ → ℝ) (T γ q : ℝ) (j : ℕ) (x : ℝ) : ℂ :=
  ((j:ℂ)^Fintype.card ι/j.factorial) *
    ∑ n ∈ Ioc 0 ⌊T*x⌋₊,
      markedExtractionWeight e (giantMarkedCenteredCore ε) Φ x n *
        (giantCandidateActiveOneMark P q (n-1):ℂ) * χ n *
        (giantCandidateActiveOneMark P q n:ℂ) *
        giantCandidateAllocationCore C (univ.biUnion P)
          (Real.exp ((Real.log x)^(6/25:ℝ))) (x^γ) j n

theorem giantCandidateActualAllocatedTerm_square_restoration_log_saving {J : Type*} [Fintype J]
    (e : J → ℝ) (he : ∀ i, 0 < e i ∧ e i < 1) {M : ℕ} (χ : DirichletCharacter ℂ M)
    {ε : ℝ} (hε : 0 < ε) (hεq : ε < 1/4) (Φ : ℝ → ℝ) (hΦ : Continuous Φ)
    {T γ q : ℝ} (hT : 0 ≤ T) (hγ : 0 < γ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (j : ℕ) (hj : 0 < j) (A : ℝ) :
    ∀ᶠ x : ℝ in atTop,∀ S : Finset (GiantCandidateGroupIndex x),
      let P (i : S) := giantCandidateGroup x i.val
      let C := giantCandidateFullPrimes x
      ‖giantCandidateActualUnguardedAllocatedTerm C P e χ ε Φ T γ q j x -
        giantCandidateActualMarkedProxyTerm C P e χ ε Φ T γ q j x‖ ≤
          x*(Real.log x)^(-A) := by
  have hG := (giantMarkedCenteredCore_interface e (fun i => (he i).2) hε hεq).mono
    (fun _ h => h.1)
  obtain ⟨D,hD,hW⟩ := markedExtractionWeight_bound e (fun i => (he i).1)
    (giantMarkedCenteredCore ε) zero_le_one hG Φ hΦ hT
  have hj1 : (1:ℝ) ≤ j := Nat.one_le_cast.mpr hj
  let c := giantCandidateGroupLogRate*Real.log (giantCandidateOneMarkBound q)
  let d := giantCandidateGroupLogRate*Real.log (j:ℝ)
  filter_upwards [hW,giantCandidateAllocationCore_actual_norm_le_fiber γ hγ j hj,
    giantCandidateActiveOneMark_actual_bound hq0 hq1,
    giantCandidateSelectedGroups_exponential_cost_eventually (j:ℝ) hj1,
    giantCandidateSelectedGroups_geometry_eventually,
    giantCandidateFullPrimes_prime_upper_eventually,giantCandidateFullPrimes_gt_W_eventually,
    giantCandidateSquareFiberMass_log_saving j T D (c+c+d) A hT hD,
    eventually_ge_atTop (0:ℝ),eventually_gt_atTop (1:ℝ)]
    with x hWx hcore hmark hcost hgeo hprime hPW hmass hx hx1
  intro S
  let C := giantCandidateFullPrimes x
  let P (i : S) := giantCandidateGroup x i.val
  let U := univ.biUnion P
  let X := ⌊T*x⌋₊
  let L := Real.log x
  let W := Real.exp (L^(6/25:ℝ))
  let F (n : ℕ) : ℂ :=
    markedExtractionWeight e (giantMarkedCenteredCore ε) Φ x n *
      (giantCandidateActiveOneMark P q (n-1):ℂ) * χ n *
      (giantCandidateActiveOneMark P q n:ℂ) * giantCandidateAllocationCore C U W (x^γ) j n
  let a : ℂ := (j:ℂ)^Fintype.card S/j.factorial
  have hX : (X:ℝ) ≤ T*x := Nat.floor_le (mul_nonneg hT hx)
  have hL : 0 < L := Real.log_pos hx1
  have hPC : U ⊆ C := giantCandidateSelectedGroups_union_subset S
  have hp : ∀ p ∈ U,p.Prime := fun p h => (hprime p (hPC h)).1
  have hPW' : ∀ p ∈ U,W < (p:ℝ) := fun p h => hPW p (hPC h)
  dsimp only
  rw [giantCandidateActualMarkedProxyTerm_eq_allocated C P hPC hp (hgeo S).1 e χ ε Φ
    T γ q j hj x hPW']
  have hF (n : ℕ) (hn : n ∈ giantCandidateSquareExceptions C X) :
      ‖F n‖ ≤ (D*L^(c+c))*((giantOrderedProductFiber j n).card:ℝ) := by
    obtain ⟨hn0,hnX,_⟩ := mem_giantCandidateSquareExceptions.mp hn
    have hnT : (n:ℝ) ≤ T*x := (Nat.cast_le.mpr hnX).trans hX
    dsimp only [F]
    simp only [norm_mul]
    calc
      _ ≤ (D*L^c*1*L^c)*((giantOrderedProductFiber j n).card:ℝ) := by
        apply mul_le_mul _ (hcore C U n hn0) (norm_nonneg _) (by positivity)
        apply mul_le_mul _ (hmark S n) (norm_nonneg _) (by positivity)
        apply mul_le_mul _ (χ.norm_le_one _) (norm_nonneg _) (by positivity)
        exact mul_le_mul (hWx n hnT) (hmark S (n-1)) (norm_nonneg _) hD
      _ = _ := by rw [Real.rpow_add hL c c]; ring
  have ha : ‖a‖ ≤ L^d := by
    dsimp only [a]
    rw [norm_div,norm_pow,Complex.norm_natCast,Complex.norm_natCast]
    have hf : (1:ℝ) ≤ j.factorial := Nat.one_le_cast.mpr (Nat.factorial_pos j)
    exact (div_le_self (by positivity) hf).trans (by simpa only [Fintype.card_coe] using hcost S)
  change ‖a*(∑ n ∈ Ioc 0 X,F n) -
    a*(∑ n ∈ (Ioc 0 X).filter (fun n => ∀ p ∈ C,¬p^2 ∣ n),F n)‖ ≤ _
  rw [← mul_sub,norm_mul]
  calc
    _ ≤ L^d*((D*L^(c+c))*giantCandidateSquareFiberMass C X j) :=
      mul_le_mul ha (giantCandidateSquareProducts_guard_error_le C X j F hF)
        (norm_nonneg _) (Real.rpow_nonneg hL.le _)
    _ = (D*L^(c+c+d))*giantCandidateSquareFiberMass C X j := by
      rw [Real.rpow_add hL (c+c) d]
      ring
    _ ≤ _ := hmass X hX

end
end ArtinMatthews
