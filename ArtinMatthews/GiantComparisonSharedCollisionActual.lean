module

public import ArtinMatthews.GiantComparisonSharedCollisionBound
public import ArtinMatthews.GiantCandidateSelectedGroups


set_option backward.privateInPublic true
@[expose] public section

/-! The actual candidate bands supply the atom bound uniformly in the
selected groups, the copied pattern and the fixed auxiliary draw. -/
namespace ArtinMatthews
open Filter Finset
open scoped BigOperators
noncomputable section

theorem giantCandidateComparisonSharedBadMass_eventually_strong (k : ℕ) (T : ℝ) (hT : 0 ≤ T) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ x : ℝ in atTop,
      ∀ S : Finset (GiantCandidateGroupIndex x),
      let P := fun i : S => giantCandidateGroup x i.val
      ∀ (C : S → Finset (Fin k)) (aux : GiantTwoSidedPatternAuxiliary P C) (w w' : ℕ),
        0 < w → 0 < w' → (w : ℝ) ≤ x^T → (w' : ℝ) ≤ x^T →
        giantComparisonSharedBadMass aux w w' ≤
          K*(Real.log x)^2*Real.exp (-(Real.log x)^(28/100 : ℝ)) := by
  let B := 2*T/Real.log (3/2)
  let A := giantCandidateGroupLogRate
  let D := 2/Real.log 2
  let K₀ := (k : ℝ)^2+(k : ℝ)*(B+k)
  have hlog32 : 0 < Real.log (3/2 : ℝ) := Real.log_pos (by norm_num)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hB : 0 ≤ B := div_nonneg (mul_nonneg zero_le_two hT) hlog32.le
  have hA : 0 ≤ A := by unfold A giantCandidateGroupLogRate; positivity
  have hD : 0 ≤ D := div_nonneg zero_le_two hlog2.le
  have hK₀ : 0 ≤ K₀ := by unfold K₀; positivity
  refine ⟨A*K₀*D, by positivity, ?_⟩
  filter_upwards [giantCandidateSelectedGroups_geometry_eventually,
    giantCandidateGroup_total_count_eventually, eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)] with x hgeometry hgroups hx hL
  intro S P C aux w w' hw hw' hwX hw'X
  let L := Real.log x
  let Y := Real.exp (L^(28/100 : ℝ))
  let E := Real.exp (-(L^(28/100 : ℝ)))
  have hL₀ : 0 < L := Real.log_pos hx
  have hY : 0 < Y := Real.exp_pos _
  obtain ⟨hdis, hmass, _⟩ := hgeometry S
  have hV (i : S) : 0 < bandReciprocalMass (P i) :=
    (div_pos hlog2 (by norm_num)).trans (hmass i).1
  have hp (i : S) (p : ℕ) (hp : p ∈ P i) : p.Prime ∧ Y ≤ (p : ℝ) := by
    have h := giantCandidateFullPrimes_range hx hL (mem_giantCandidateFullPrimes.mpr ⟨i.val,hp⟩)
    exact ⟨h.1,h.2.1⟩
  have hw₀ : 0 < (w : ℝ) := Nat.cast_pos.mpr hw
  have hw'₀ : 0 < (w' : ℝ) := Nat.cast_pos.mpr hw'
  have hlogw : Real.log (w : ℝ) ≤ T*L :=
    (Real.log_le_log hw₀ hwX).trans_eq (Real.log_rpow (zero_lt_one.trans hx) T)
  have hlogw' : Real.log (w' : ℝ) ≤ T*L :=
    (Real.log_le_log hw'₀ hw'X).trans_eq (Real.log_rpow (zero_lt_one.trans hx) T)
  have hlogprod : Real.log ((w*w' : ℕ) : ℝ) ≤ 2*T*L := by
    rw [Nat.cast_mul, Real.log_mul hw₀.ne' hw'₀.ne']
    linarith only [hlogw, hlogw']
  have hcap : Real.log ((w*w' : ℕ) : ℝ)/Real.log (3/2) ≤ B*L := by
    calc
      _ ≤ (2*T*L)/Real.log (3/2) := div_le_div_of_nonneg_right hlogprod hlog32.le
      _ = _ := by unfold B; ring
  have hcount : (Fintype.card S : ℝ) ≤ A*L := by
    rw [Fintype.card_coe]
    have hs : (S.card : ℝ) ≤ A*Real.log L := (Nat.cast_le.mpr (card_le_univ S)).trans hgroups
    exact hs.trans (mul_le_mul_of_nonneg_left
      ((Real.log_le_sub_one_of_pos hL₀).trans (by linarith)) hA)
  have hatom (i : S) : 1/(Y*bandReciprocalMass (P i)) ≤ D*E := by
    calc
      _ ≤ 1/(Y*(Real.log 2/2)) := one_div_le_one_div_of_le
        (mul_pos hY (div_pos hlog2 (by norm_num)))
        (mul_le_mul_of_nonneg_left (hmass i).1.le hY.le)
      _ = _ := by
        unfold D E Y
        rw [Real.exp_neg]
        field_simp [hlog2.ne', Real.exp_ne_zero]
  have hsize (U : Finset (Fin k)) : (U.card : ℝ) ≤ k := by
    exact Nat.cast_le.mpr (by simpa only [card_univ, Fintype.card_fin] using card_le_univ U)
  have hfactor (i : S) : ((univ \ C i).card : ℝ)^2 + ((univ \ C i).card : ℝ)*
      (Real.log ((w*w' : ℕ) : ℝ)/Real.log (3/2) + (C i).card) ≤ K₀*L := by
    have hs := hsize (univ \ C i)
    have hc := hsize (C i)
    have hforbidden : Real.log ((w*w' : ℕ) : ℝ)/Real.log (3/2)+(C i).card ≤ (B+k)*L := by
      apply (add_le_add hcap hc).trans
      nlinarith only [mul_le_mul_of_nonneg_left hL (Nat.cast_nonneg k)]
    have hmul : ((univ \ C i).card : ℝ)*
        (Real.log ((w*w' : ℕ) : ℝ)/Real.log (3/2)+(C i).card) ≤ (k : ℝ)*((B+k)*L) :=
      (mul_le_mul_of_nonneg_left hforbidden (Nat.cast_nonneg _)).trans
        (mul_le_mul_of_nonneg_right hs (by positivity))
    apply (add_le_add (pow_le_pow_left₀ (Nat.cast_nonneg _) hs 2) hmul).trans
    unfold K₀
    nlinarith only [mul_le_mul_of_nonneg_left hL (sq_nonneg (k : ℝ))]
  change giantComparisonSharedBadMass aux w w' ≤ (A*K₀*D)*L^2*E
  calc
    _ ≤ ∑ i : S, (((univ \ C i).card : ℝ)^2 + ((univ \ C i).card : ℝ)*
        (Real.log ((w*w' : ℕ) : ℝ)/Real.log (3/2)+(C i).card)) *
        (1/(Y*bandReciprocalMass (P i))) :=
      giantComparisonSharedBadMass_le (fun i p h => (hp i p h).1) hdis hV aux hw hw' hY
        (fun i p h => (hp i p h).2)
    _ ≤ ∑ _i : S, (K₀*L)*(D*E) := by
      apply sum_le_sum
      intro i _
      exact mul_le_mul (hfactor i) (hatom i)
        (one_div_nonneg.mpr (mul_nonneg hY.le (hV i).le)) (mul_nonneg hK₀ hL₀.le)
    _ = (Fintype.card S : ℝ)*((K₀*L)*(D*E)) := by simp only [sum_const,card_univ,nsmul_eq_mul]
    _ ≤ (A*L)*((K₀*L)*(D*E)) := mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = _ := by ring

theorem giantCandidateComparisonSharedBadMass_eventually (k : ℕ) (T : ℝ) (hT : 0 ≤ T) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ x : ℝ in atTop,
      ∀ S : Finset (GiantCandidateGroupIndex x),
      let P := fun i : S => giantCandidateGroup x i.val
      ∀ (C : S → Finset (Fin k)) (aux : GiantTwoSidedPatternAuxiliary P C) (w w' : ℕ),
        0 < w → 0 < w' → (w : ℝ) ≤ x^T → (w' : ℝ) ≤ x^T →
        giantComparisonSharedBadMass aux w w' ≤
          K*(Real.log x)^2*Real.exp (-(Real.log x)^(27/100 : ℝ)) := by
  obtain ⟨K,hK,hbound⟩ := giantCandidateComparisonSharedBadMass_eventually_strong k T hT
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound,Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)] with x hb hL
  intro S P C aux w w' hw hw' hwX hw'X
  apply (hb S C aux w w' hw hw' hwX hw'X).trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hK (sq_nonneg _))
  exact Real.exp_le_exp.mpr (neg_le_neg (Real.rpow_le_rpow_of_exponent_le hL (by norm_num)))

end
end ArtinMatthews
