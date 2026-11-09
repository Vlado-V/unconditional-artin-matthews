module

public import ArtinMatthews.GiantCandidateSquareRemoval
public import ArtinMatthews.GiantCandidateSquareRestoration
public import ArtinMatthews.GiantCandidateAllocationCorrelation


set_option backward.privateInPublic true
@[expose] public section

/-! The expanded source term reduces to the literal unguarded two-sided
correlation after a negligible error. The fixed character remains
evaluated at the original right endpoint. -/
namespace ArtinMatthews
open Filter Finset
open scoped BigOperators
noncomputable section

def giantCandidateActualUnguardedShiftedCorrelation {J ι : Type*} [Fintype J] [Fintype ι]
    (C : Finset ℕ) (P : ι → Finset ℕ) (e : J → ℝ) {M : ℕ} (χ : DirichletCharacter ℂ M)
    (ε : ℝ) (Φ : ℝ → ℝ) (T γ q : ℝ) (j : ℕ) (x : ℝ) : ℂ :=
  ∑ u ∈ Ioc 0 ⌊T*x⌋₊,
    (((u:ℝ)/x*Φ ((u:ℝ)/x):ℝ):ℂ)/(u:ℂ) *
      giantCandidateFirstEndpoint e ε x u *
      (giantCandidateActiveOneMark P q u : ℂ) * χ (u+1:ℕ) *
      (giantCandidateActiveOneMark P q (u+1) : ℂ) *
      giantCandidateAllocationCore C (univ.biUnion P)
        (Real.exp ((Real.log x)^(6/25:ℝ))) (x^γ) j (u+1)

theorem giantCandidateActualUnguardedAllocatedTerm_eq_shifted {J ι : Type*}
    [Fintype J] [Fintype ι] (C : Finset ℕ) (P : ι → Finset ℕ)
    (e : J → ℝ) {M : ℕ} (χ : DirichletCharacter ℂ M)
    (ε : ℝ) (Φ : ℝ → ℝ) (T γ q : ℝ) (j : ℕ) (x : ℝ)
    (hT : 0 ≤ T) (hx : 1 ≤ x) (hΦzero : Φ 0 = 0) (hhigh : ∀ t,T<t → Φ t=0) :
    giantCandidateActualUnguardedAllocatedTerm C P e χ ε Φ (T+1) γ q j x =
      ((j:ℂ)^Fintype.card ι/j.factorial) *
        ((x:ℂ)*giantCandidateActualUnguardedShiftedCorrelation C P e χ ε Φ T γ q j x) := by
  unfold giantCandidateActualUnguardedAllocatedTerm
  apply congrArg (fun s : ℂ => ((j:ℂ)^Fintype.card ι/j.factorial)*s)
  let W := Real.exp ((Real.log x)^(6/25:ℝ))
  let f (n : ℕ) : ℂ :=
    markedExtractionWeight e (giantMarkedCenteredCore ε) Φ x n *
      (giantCandidateActiveOneMark P q (n-1):ℂ) * χ n *
      (giantCandidateActiveOneMark P q n:ℂ) *
      giantCandidateAllocationCore C (univ.biUnion P) W (x^γ) j n
  have hF (n : ℕ) (hn : T*x < ((n-1:ℕ):ℝ)) : f n=0 := by
    unfold f
    rw [markedExtractionWeight_eq_zero_of_past e (giantMarkedCenteredCore ε) Φ
      (zero_lt_one.trans_le hx) hhigh hn]
    simp only [zero_mul]
  have hr := giantExtraction_predecessor_reindex T x hT hx (fun _ => True) f hF
  simp only [filter_true] at hr
  change (∑ n ∈ Ioc 0 ⌊(T+1)*x⌋₊,f n) = _
  rw [hr]
  have hsub : Ioc 0 ⌊T*x⌋₊ ⊆ Icc 0 ⌊T*x⌋₊ :=
    fun _ h => mem_Icc.mpr ⟨Nat.zero_le _,(mem_Ioc.mp h).2⟩
  have hcut : (∑ u ∈ Ioc 0 ⌊T*x⌋₊,f (u+1)) = ∑ u ∈ Icc 0 ⌊T*x⌋₊,f (u+1) := by
    apply sum_subset hsub
    intro u hu hneg
    have he : u=0 := by
      by_contra h
      exact hneg (mem_Ioc.mpr ⟨Nat.pos_of_ne_zero h,(mem_Icc.mp hu).2⟩)
    subst u
    simp only [f,markedExtractionWeight,Nat.zero_add,Nat.sub_self,Nat.cast_zero,
      zero_div,hΦzero,Complex.ofReal_zero,zero_mul]
  rw [← hcut,giantCandidateActualUnguardedShiftedCorrelation,Finset.mul_sum]
  apply sum_congr rfl
  intro u hu
  have hu0 : (u:ℂ) ≠ 0 := by exact_mod_cast (mem_Ioc.mp hu).1.ne'
  have hx0 : x ≠ 0 := (zero_lt_one.trans_le hx).ne'
  have hscale : (x:ℂ)*((((u:ℝ)/x*Φ ((u:ℝ)/x):ℝ):ℂ)/(u:ℂ)) = (Φ ((u:ℝ)/x):ℂ) := by
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hx0,hu0]
  simp only [f,W,giantCandidateFirstEndpoint,markedExtractionWeight,Nat.add_sub_cancel]
  rw [← hscale]
  ring

theorem giantCandidateActualExpandedProxyTerm_shifted_log_saving {J : Type*} [Fintype J]
    (e : J → ℝ) (he : ∀ i, 0 < e i ∧ e i < 1) {M : ℕ} (χ : DirichletCharacter ℂ M)
    {ε : ℝ} (hε : 0 < ε) (hεq : ε < 1/4) (Φ : ℝ → ℝ) (hΦ : Continuous Φ)
    {T γ q : ℝ} (hT : 0 ≤ T) (hΦzero : Φ 0=0) (hhigh : ∀ t,T<t → Φ t=0)
    (hγ : 0 < γ) (hq0 : 0 ≤ q) (hq1 : q < 1) (j : ℕ) (hj : 0 < j) (A : ℝ) :
    ∀ᶠ x : ℝ in atTop,∀ S : Finset (GiantCandidateGroupIndex x),
      let P (i : S) := giantCandidateGroup x i.val
      let C := giantCandidateFullPrimes x
      ‖giantCandidateActualUnguardedMarkedProxyTerm C P e χ ε Φ (T+1) γ q j x -
        ((j:ℂ)^S.card/j.factorial) *
          ((x:ℂ)*giantCandidateActualUnguardedShiftedCorrelation C P e χ ε Φ T γ q j x)‖ ≤
            x*(Real.log x)^(-A) := by
  have hT1 : 0 ≤ T+1 := by positivity
  filter_upwards [giantCandidateActualMarkedProxyTerm_square_guard_log_saving e he χ hε hεq Φ hΦ
      hT1 hγ hq0 hq1 j hj (A+1),
    giantCandidateActualAllocatedTerm_square_restoration_log_saving e he χ hε hεq Φ hΦ
      hT1 hγ hq0 hq1 j hj (A+1),
    eventually_ge_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (2:ℝ))]
    with x hrem hrest hx hL
  intro S
  let P (i : S) := giantCandidateGroup x i.val
  let C := giantCandidateFullPrimes x
  let L := Real.log x
  let f := giantCandidateActualUnguardedMarkedProxyTerm C P e χ ε Φ (T+1) γ q j x
  let g := giantCandidateActualMarkedProxyTerm C P e χ ε Φ (T+1) γ q j x
  let h := giantCandidateActualUnguardedAllocatedTerm C P e χ ε Φ (T+1) γ q j x
  have hshift : h = ((j:ℂ)^S.card/j.factorial) *
      ((x:ℂ)*giantCandidateActualUnguardedShiftedCorrelation C P e χ ε Φ T γ q j x) := by
    simpa only [h,Fintype.card_coe] using giantCandidateActualUnguardedAllocatedTerm_eq_shifted
      C P e χ ε Φ T γ q j x hT hx hΦzero hhigh
  dsimp only
  rw [← hshift]
  change ‖f-h‖ ≤ x*L^(-A)
  have hL0 : 0 < L := (by norm_num : (0:ℝ)<2).trans_le hL
  have hp : L^(-(A+1)) = L^(-A)*L⁻¹ := by
    rw [show -(A+1) = -A + -1 by ring,Real.rpow_add hL0,Real.rpow_neg_one]
  have hfac : (2:ℝ)*L⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv]
    exact (div_le_one hL0).mpr hL
  calc
    _ ≤ ‖f-g‖+‖h-g‖ := by
      simpa only [norm_sub_rev g h] using norm_sub_le_norm_sub_add_norm_sub f g h
    _ ≤ x*L^(-(A+1))+x*L^(-(A+1)) := add_le_add (hrem S) (hrest S)
    _ = (x*L^(-A))*(2*L⁻¹) := by rw [hp]; ring
    _ ≤ _ := mul_le_of_le_one_right (by positivity) hfac

end
end ArtinMatthews
