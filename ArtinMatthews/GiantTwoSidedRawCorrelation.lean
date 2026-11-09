module

public import ArtinMatthews.GiantTwoSidedRawKernelActual
public import ArtinMatthews.GiantTwoSidedRawPositionCutoff
public import ArtinMatthews.GiantTwoSidedRawMarkWeightError
public import ArtinMatthews.GiantTwoSidedRawMass
public import ArtinMatthews.GiantCandidateUnguardedCorrelation


set_option backward.privateInPublic true
@[expose] public section

/-! The actual raw physical graph sum, with the fixed character and
literal endpoint weights, gives the original normalized shifted
correlation to every fixed logarithmic order. -/
namespace ArtinMatthews
open Finset Filter
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def giantCandidateActualRawPhysicalSum {J ι : Type*} [Fintype J] [Fintype ι] [DecidableEq ι]
    (C : Finset ℕ) (P : ι → Finset ℕ) (e : J → ℝ) {m : ℕ} (χ : DirichletCharacter ℂ m)
    (ε : ℝ) (Φ : ℝ → ℝ) (T γ q : ℝ) (j k : ℕ) (x : ℝ) : ℂ :=
  let N := ⌊T*x⌋₊
  let Z := giantTwoSidedRawPositionBox P k N
  let Z' := giantTwoSidedRawPositionBox P k (N+1)
  let F := giantCandidateFirstEndpoint e ε x
  let G := giantCandidateAllocationCore C (univ.biUnion P)
    (Real.exp ((Real.log x)^(6/25:ℝ))) (x^γ) j
  ∑ r : GiantTwoSidedRawPhysicalEdge P k Z Z',
    giantTwoSidedRawPhysicalTerm x q (fun t => ((t*Φ t:ℝ):ℂ)) χ F G r

theorem giantCandidateActualRawPhysicalSum_log_saving {J : Type*} [Fintype J]
    (e : J → ℝ) (he : ∀ i,0 < e i ∧ e i ≤ 1/5) {ε : ℝ} (hε : 0 < ε) (hεq : ε < 1/4)
    {m : ℕ} (hm : 0 < m) (χ : DirichletCharacter ℂ m) (Φ : ℝ → ℝ) (hΦ : Continuous Φ)
    {T γ q : ℝ} (hT : 0 ≤ T) (hhigh : ∀ t,T<t → Φ t=0)
    (hγ : 0 < γ) (hq : 0 < q) (hq1 : q < 1) (j : ℕ) (hj : 0 < j) (k : ℕ) (A : ℝ) :
    ∀ᶠ x : ℝ in atTop,∀ S : Finset (GiantCandidateGroupIndex x),
      let P (i : S) := giantCandidateGroup x i.val
      let C := giantCandidateFullPrimes x
      ‖giantCandidateActualRawPhysicalSum C P e χ ε Φ T γ q j k x -
        giantCandidateActualUnguardedShiftedCorrelation C P e χ ε Φ T γ q j x‖ ≤
          (Real.log x)^(-A) := by
  obtain ⟨B,_,habs⟩ := giantCandidateRawHarmonic_absolute_mass e
    (fun i => ⟨(he i).1,(he i).2.trans_lt (by norm_num)⟩) hε hεq χ Φ hΦ hT hγ hq.le hq1 j hj
  let b := 2*(giantCandidateGroupLogRate*Real.log (giantCandidateOneMarkBound q))+(j:ℝ)
  let Ψ (t : ℝ) : ℂ := ((t*Φ t:ℝ):ℂ)
  filter_upwards [giantCandidateRawPhysical_sum_eq_shared_eventually e (fun i => (he i).2)
      hεq hm χ γ j q Ψ,
    giantCandidateNormalizedMarkWeight_log_saving k T hT hq hq1.le (A+b+1),
    giantCandidateFullPrimes_prime_upper_eventually,habs,eventually_gt_atTop (0:ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (max 1 B)]
    with x heq hrest hprime hmass hx hL
  intro S
  let P (i : S) := giantCandidateGroup x i.val
  let C := giantCandidateFullPrimes x
  let F := giantCandidateFirstEndpoint e ε x
  let G := giantCandidateAllocationCore C (univ.biUnion P)
    (Real.exp ((Real.log x)^(6/25:ℝ))) (x^γ) j
  let K := giantTwoSidedRawPositionKernel x Ψ χ F G
  let L := Real.log x
  let N := ⌊T*x⌋₊
  let Z := giantTwoSidedRawPositionBox P k N
  let Z' := giantTwoSidedRawPositionBox P k (N+1)
  let N' := max N (giantTwoSidedSharedProductMax P k*N)
  have hP (i : S) (p : ℕ) (hp : p∈P i) : p.Prime :=
    (hprime p (mem_giantCandidateFullPrimes.mpr ⟨i.val,hp⟩)).1
  have hZ : Z ⊆ Ioc 0 N' := by
    intro n hn
    exact mem_Ioc.mpr ⟨(mem_Ioc.mp hn).1,(mem_Ioc.mp hn).2.trans (le_max_right _ _)⟩
  have hcut (w : ℕ) (hw : N<w) : Ψ ((w:ℝ)/x)=0 :=
    giantTwoSidedRawPositionKernel_cutoff hx hT Φ hhigh w hw
  have hraw : giantCandidateActualRawPhysicalSum C P e χ ε Φ T γ q j k x =
      ∑ w ∈ Ioc 0 N,K w*(giantTwoSidedNormalizedMarkWeight P k q w:ℂ) := by
    calc
      _ = ∑ a : GiantTwoSidedRawSharedEdge P k N' Z Z',giantTwoSidedRawSharedTerm x q Ψ χ F G a :=
        heq S k N' Z Z' hZ
      _ = ∑ a : GiantTwoSidedRawSharedEdge P k N Z Z',giantTwoSidedRawSharedTerm x q Ψ χ F G a :=
        giantTwoSidedRawShared_sum_eq_of_cutoff (le_max_left _ _) x q Ψ χ F G hcut
      _ = _ := giantTwoSidedRawShared_sum_eq_harmonic (giantTwoSidedRawPositionBox_cover hP) x q Ψ χ F G
  have hcorr : giantCandidateActualUnguardedShiftedCorrelation C P e χ ε Φ T γ q j x =
      ∑ w ∈ Ioc 0 N,K w*((giantCandidateActiveOneMark P q w*
        giantCandidateActiveOneMark P q (w+1):ℝ):ℂ) := by
    unfold giantCandidateActualUnguardedShiftedCorrelation
    apply sum_congr rfl
    intro w _
    simp only [K,giantTwoSidedRawPositionKernel,Complex.ofReal_mul,Ψ,F,G]
    ring
  have hL0 : 0 < L := zero_lt_one.trans_le ((le_max_left _ _).trans hL)
  have hBL : B ≤ L := (le_max_right _ _).trans hL
  have hpow : L^(-(A+b+1))*L^b = L^(-A)*L⁻¹ := by
    rw [← Real.rpow_add hL0,show -(A+b+1)+b = -A + -1 by ring,
      Real.rpow_add hL0,Real.rpow_neg_one]
  change ‖giantCandidateActualRawPhysicalSum C P e χ ε Φ T γ q j k x -
    giantCandidateActualUnguardedShiftedCorrelation C P e χ ε Φ T γ q j x‖ ≤ L^(-A)
  rw [hraw,hcorr]
  calc
    _ ≤ L^(-(A+b+1))*(∑ w ∈ Ioc 0 N,‖K w‖*(giantCandidateActiveOneMark P q w*
        giantCandidateActiveOneMark P q (w+1))) :=
      giantTwoSidedRawHarmonic_sum_error P k N q _ K (hrest S)
    _ ≤ L^(-(A+b+1))*(B*L^b) := mul_le_mul_of_nonneg_left (hmass S) (Real.rpow_nonneg hL0.le _)
    _ = L^(-A)*(B/L) := by
      rw [mul_left_comm (L^(-(A+b+1))) B,hpow,div_eq_mul_inv]
      ring
    _ ≤ _ := mul_le_of_le_one_right (Real.rpow_nonneg hL0.le _) ((div_le_one hL0).mpr hBL)

end
end ArtinMatthews
