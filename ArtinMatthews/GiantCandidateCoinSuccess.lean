module

public import ArtinMatthews.GiantCandidateOneMarkBounds


set_option backward.privateInPublic true
@[expose] public section

/-! The literal candidate coin tests use the two actual endpoint counts.
A single fixed scale makes these genuine probabilities uniformly in
the growing candidate families. -/
namespace ArtinMatthews
open Finset Filter
open scoped BigOperators
noncomputable section

def giantCandidateCoinTest (c q : ℝ) (j : ℕ) (V : ℝ) (a b : ℕ) : ℝ :=
  c*((a:ℝ)/V*q^(a-1))*((b:ℝ)/V*(q/(j:ℝ))^(b-1))

def giantCandidateCoinScale (q : ℝ) (j : ℕ) : ℝ :=
  (giantCandidateOneMarkBound q * giantCandidateOneMarkBound (q/(j:ℝ)))⁻¹

def giantCandidateCoinSuccess (x c q : ℝ) (j v : ℕ) (i : GiantCandidateGroupIndex x) : ℝ :=
  let P := giantCandidateGroup x i
  giantCandidateCoinTest c q j (bandReciprocalMass P) (bandCount P (v-1)) (bandCount P v)

theorem giantCandidateCoinTest_one_one (c q : ℝ) (j : ℕ) {V : ℝ} (hV : V ≠ 0) :
    giantCandidateCoinTest c q j V 1 1 = c/V^2 := by
  simp only [giantCandidateCoinTest,Nat.cast_one,Nat.sub_self,pow_zero,mul_one]
  field_simp

theorem giantCandidateCoinScale_bounds {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (j : ℕ) (hj : 0 < j) :
    0 < giantCandidateCoinScale q j ∧ giantCandidateCoinScale q j ≤ 1 ∧
      giantCandidateCoinScale q j * giantCandidateOneMarkBound q *
        giantCandidateOneMarkBound (q/(j:ℝ)) = 1 := by
  have hj1 : (1:ℝ) ≤ j := Nat.one_le_cast.mpr hj
  have hqj0 : 0 ≤ q/(j:ℝ) := div_nonneg hq0 (Nat.cast_nonneg _)
  have hqj1 : q/(j:ℝ) < 1 := (div_le_self hq0 hj1).trans_lt hq1
  have hB := giantCandidateOneMarkBound_one_le hq0 hq1
  have hB' := giantCandidateOneMarkBound_one_le hqj0 hqj1
  have hprod : 1 ≤ giantCandidateOneMarkBound q * giantCandidateOneMarkBound (q/(j:ℝ)) := by
    simpa only [one_mul] using mul_le_mul hB hB' zero_le_one (zero_le_one.trans hB)
  have hpos := zero_lt_one.trans_le hprod
  unfold giantCandidateCoinScale
  refine ⟨inv_pos.mpr hpos,(inv_le_one₀ hpos).mpr hprod,?_⟩
  rw [mul_assoc,inv_mul_cancel₀ hpos.ne']

theorem giantCandidateCoinTest_mem_unitInterval {c q V : ℝ} (hc : 0 ≤ c)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (j : ℕ) (hj : 0 < j)
    (hV : Real.log 2/2 ≤ V)
    (hscale : c*giantCandidateOneMarkBound q*giantCandidateOneMarkBound (q/(j:ℝ)) ≤ 1)
    (a b : ℕ) : giantCandidateCoinTest c q j V a b ∈ Set.Icc (0:ℝ) 1 := by
  have hV0 : 0 < V := (div_pos (Real.log_pos (by norm_num)) (by norm_num)).trans_le hV
  have hj1 : (1:ℝ) ≤ j := Nat.one_le_cast.mpr hj
  have hqj0 : 0 ≤ q/(j:ℝ) := div_nonneg hq0 (Nat.cast_nonneg _)
  have hqj1 : q/(j:ℝ) < 1 := (div_le_self hq0 hj1).trans_lt hq1
  have ha := giantCandidateOneMarkFactor_le hq0 hq1 hV a
  have hb := giantCandidateOneMarkFactor_le hqj0 hqj1 hV b
  refine ⟨by unfold giantCandidateCoinTest; positivity,?_⟩
  exact (mul_le_mul (mul_le_mul_of_nonneg_left ha hc) hb (by positivity)
    (mul_nonneg hc (zero_le_one.trans (giantCandidateOneMarkBound_one_le hq0 hq1)))).trans hscale

theorem giantCandidateCoinSuccess_actual_unitInterval {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (j : ℕ) (hj : 0 < j) :
    ∀ᶠ x : ℝ in atTop, ∀ (i : GiantCandidateGroupIndex x) (v : ℕ),
      giantCandidateCoinSuccess x (giantCandidateCoinScale q j) q j v i ∈ Set.Icc (0:ℝ) 1 := by
  obtain ⟨hc,_,hs⟩ := giantCandidateCoinScale_bounds hq0 hq1 j hj
  filter_upwards [giantCandidateGroup_mass_eventually] with x hx
  intro i v
  exact giantCandidateCoinTest_mem_unitInterval hc.le hq0 hq1 j hj (hx i).1.le hs.le _ _

theorem giantCandidateCoinSuccess_prod (x c q : ℝ) (j v : ℕ)
    (S : Finset (GiantCandidateGroupIndex x)) :
    (∏ i ∈ S,giantCandidateCoinSuccess x c q j v i) =
      c^S.card *
        giantCandidateActiveOneMark (fun i : S => giantCandidateGroup x i.val) q (v-1) *
        giantCandidateActiveOneMark (fun i : S => giantCandidateGroup x i.val) (q/(j:ℝ)) v := by
  let A (i : GiantCandidateGroupIndex x) :=
    let G := giantCandidateGroup x i
    (bandCount G (v-1):ℝ)/bandReciprocalMass G*q^(bandCount G (v-1)-1)
  let B (i : GiantCandidateGroupIndex x) :=
    let G := giantCandidateGroup x i
    (bandCount G v:ℝ)/bandReciprocalMass G*(q/(j:ℝ))^(bandCount G v-1)
  change (∏ i ∈ S,c*A i*B i) = c^S.card*(∏ i : S,A i.val)*(∏ i : S,B i.val)
  rw [Finset.prod_coe_sort S A,Finset.prod_coe_sort S B]
  simp only [prod_mul_distrib,prod_const]

end
end ArtinMatthews
