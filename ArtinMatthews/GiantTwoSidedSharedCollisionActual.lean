module

public import ArtinMatthews.GiantTwoSidedSharedCollision
public import ArtinMatthews.GiantCandidateSelectedGroups


set_option backward.privateInPublic true
@[expose] public section

/-! The actual candidate lower endpoint makes the harmonic exceptional
mass exponentially small in a positive power of log x. The bound is
uniform in every performed subset and each actual stripped position. -/
namespace ArtinMatthews
open Filter Finset
open scoped BigOperators
noncomputable section

theorem giantCandidateSharedBadMass_eventually (k : ℕ) (T : ℝ) (hT : 0 ≤ T) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ᶠ x : ℝ in atTop,
      ∀ (S : Finset (GiantCandidateGroupIndex x)) (w : ℕ),w∈Ioc 0 ⌊T*x⌋₊ →
      giantTwoSidedSharedBadMass (fun i : S => giantCandidateGroup x i.val) k w ≤
        C*(Real.log x)^2*Real.exp (-(Real.log x)^(28/100:ℝ)) := by
  let B := 2*(1+Real.log (T+1))/Real.log (3/2)
  let A := giantCandidateGroupLogRate
  let D := 2/Real.log 2
  let C := ((k:ℝ)^2+(k:ℝ)*B)*A*D
  have hlogT : 0 ≤ Real.log (T+1) := Real.log_nonneg (by linarith)
  have hB : 0 ≤ B := div_nonneg (by positivity) (Real.log_pos (by norm_num)).le
  have hA : 0 ≤ A := by unfold A giantCandidateGroupLogRate; positivity
  have hD : 0 ≤ D := by unfold D; positivity
  refine ⟨C,by unfold C; positivity,?_⟩
  filter_upwards [giantCandidateGroup_mass_eventually,giantCandidateGroup_total_count_eventually,
    eventually_gt_atTop (1:ℝ),Real.tendsto_log_atTop.eventually_ge_atTop (1:ℝ)]
    with x hmass hgroups hx hL
  intro S w hw
  let P (i : S) := giantCandidateGroup x i.val
  let L := Real.log x
  let Y := Real.exp (L^(28/100:ℝ))
  let E := Real.exp (-(L^(28/100:ℝ)))
  have hL0 : 0 < L := Real.log_pos hx
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hY : 0 < Y := Real.exp_pos _
  have hE : 0 ≤ E := Real.exp_nonneg _
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hV (i : S) : 0 < bandReciprocalMass (P i) :=
    (div_pos h2 (by norm_num)).trans (hmass i.val).1
  have hp (i : S) (p : ℕ) (hp : p∈P i) :
      p.Prime ∧ Y ≤ (p:ℝ) := by
    have h := giantCandidateFullPrimes_range hx hL (mem_giantCandidateFullPrimes.mpr ⟨i.val,hp⟩)
    exact ⟨h.1,h.2.1⟩
  obtain ⟨hw0,hwN⟩ := mem_Ioc.mp hw
  have hwX : (w:ℝ) ≤ T*x :=
    (Nat.cast_le.mpr hwN).trans (Nat.floor_le (mul_nonneg hT hx0.le))
  have hX (v : ℝ) (hv : v ≤ (w:ℝ)+1) : v ≤ (T+1)*x := by nlinarith only [hwX,hv,hx.le]
  have hT1 : 0 < T+1 := by linarith
  have hwpos : 0 < (w:ℝ) := Nat.cast_pos.mpr hw0
  have hwpos' : 0 < ((w+1:ℕ):ℝ) := Nat.cast_pos.mpr (Nat.succ_pos _)
  have hlogw : Real.log (w:ℝ) ≤ Real.log (T+1)+L :=
    (Real.log_le_log hwpos (hX _ (by linarith))).trans_eq (Real.log_mul hT1.ne' hx0.ne')
  have hlogw' : Real.log ((w+1:ℕ):ℝ) ≤ Real.log (T+1)+L := by
    apply (Real.log_le_log hwpos' (hX _ (by simp only [Nat.cast_add,Nat.cast_one,le_refl]))).trans_eq
    exact Real.log_mul hT1.ne' hx0.ne'
  have hlogP : Real.log ((w*(w+1):ℕ):ℝ) ≤ 2*(1+Real.log (T+1))*L := by
    rw [Nat.cast_mul,Real.log_mul hwpos.ne' hwpos'.ne']
    nlinarith only [hlogw,hlogw',mul_le_mul_of_nonneg_left hL hlogT]
  have hcap : Real.log ((w*(w+1):ℕ):ℝ)/Real.log (3/2) ≤ B*L := by
    calc
      _ ≤ (2*(1+Real.log (T+1))*L)/Real.log (3/2) :=
        div_le_div_of_nonneg_right hlogP (Real.log_nonneg (by norm_num))
      _ = _ := by unfold B; ring
  have hcount : (Fintype.card S:ℝ) ≤ A*L := by
    rw [Fintype.card_coe]
    have hs : (S.card:ℝ) ≤ A*Real.log L := (Nat.cast_le.mpr (card_le_univ S)).trans hgroups
    exact hs.trans (mul_le_mul_of_nonneg_left
      ((Real.log_le_sub_one_of_pos hL0).trans (by linarith)) hA)
  have hsum : (∑ i : S,1/(Y*bandReciprocalMass (P i))) ≤ A*L*D*E := by
    calc
      _ ≤ ∑ _i : S,D*E := by
        apply sum_le_sum
        intro i _
        calc
          _ ≤ 1/(Y*(Real.log 2/2)) := one_div_le_one_div_of_le
            (mul_pos hY (div_pos h2 (by norm_num)))
            (mul_le_mul_of_nonneg_left (hmass i.val).1.le hY.le)
          _ = _ := by
            unfold D E Y
            rw [Real.exp_neg]
            field_simp [h2.ne',Real.exp_ne_zero]
      _ = (Fintype.card S:ℝ)*(D*E) := by simp only [sum_const,card_univ,nsmul_eq_mul]
      _ ≤ (A*L)*(D*E) := mul_le_mul_of_nonneg_right hcount (mul_nonneg hD hE)
      _ = _ := by ring
  have hfactor : (k:ℝ)^2+(k:ℝ)*(Real.log ((w*(w+1):ℕ):ℝ)/Real.log (3/2)) ≤
      ((k:ℝ)^2+(k:ℝ)*B)*L := by
    calc
      _ ≤ (k:ℝ)^2+(k:ℝ)*(B*L) := add_le_add le_rfl (mul_le_mul_of_nonneg_left hcap (Nat.cast_nonneg k))
      _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left hL (sq_nonneg (k:ℝ))]
  change giantTwoSidedSharedBadMass P k w ≤ C*L^2*E
  calc
    _ ≤ ((k:ℝ)^2+(k:ℝ)*(Real.log ((w*(w+1):ℕ):ℝ)/Real.log (3/2))) *
        ∑ i : S,1/(Y*bandReciprocalMass (P i)) :=
      giantTwoSidedSharedBadMass_le P (fun i p h => (hp i p h).1) hV k w hw0 hY
        (fun i p h => (hp i p h).2)
    _ ≤ (((k:ℝ)^2+(k:ℝ)*B)*L)*(A*L*D*E) := by
      apply mul_le_mul hfactor hsum
      · exact sum_nonneg (fun i _ => one_div_nonneg.mpr (mul_nonneg hY.le (hV i).le))
      · positivity
    _ = _ := by unfold C; ring

end
end ArtinMatthews
