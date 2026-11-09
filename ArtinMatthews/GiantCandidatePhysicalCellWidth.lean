module

public import ArtinMatthews.GiantTwoSidedRootMargin


set_option backward.privateInPublic true
@[expose] public section

/-! The source displacement gives a concrete integer cell width. Its
size and the endpoint supremum cost are bounded after the true moment root. -/
namespace ArtinMatthews
open Filter
open scoped Asymptotics Topology
noncomputable section

def giantCandidatePhysicalCellWidth (k : ℕ) (Cstep x : ℝ) : ℕ :=
  ⌈(Real.log x)^(max Cstep 0) *
    Real.exp (((k : ℝ)*giantCandidateGroupLogRate)*(Real.log x)^(46/100 : ℝ))⌉₊

theorem giantCandidatePhysicalCellWidth_eventually (k : ℕ) (Cstep : ℝ) :
    ∀ᶠ x : ℝ in atTop,
      0 < giantCandidatePhysicalCellWidth k Cstep x ∧
      ∀ groups : Finset (GiantCandidateGroupIndex x),
        let P := fun j : ↥groups => giantCandidateGroup x j.val
        ∀ (ell : ℕ) (C : ↥groups → Finset (Fin k)) (a : MarkedPhysicalMarking P (k+ell))
          (aux : GiantTwoSidedPatternAuxiliary P C) (step : ℤ),
          (step.natAbs : ℝ) ≤ (Real.log x)^Cstep →
          step.natAbs * giantTwoSidedPatternDilation C a aux ≤ giantCandidatePhysicalCellWidth k Cstep x := by
  filter_upwards [giantCandidatePatternDilation_exp_bound k,
    Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)] with x hD hL
  have hL0 : 0 < Real.log x := zero_lt_one.trans_le hL
  refine ⟨Nat.ceil_pos.mpr (mul_pos (Real.rpow_pos_of_pos hL0 _) (Real.exp_pos _)),?_⟩
  intro groups
  dsimp only
  intro ell C a aux step hstep
  apply (Nat.cast_le (α := ℝ)).mp
  rw [Nat.cast_mul]
  apply le_trans _ (Nat.le_ceil _)
  exact mul_le_mul (hstep.trans (Real.rpow_le_rpow_of_exponent_le hL (le_max_left _ _)))
    (hD groups ell C a aux) (Nat.cast_nonneg _) (Real.rpow_nonneg hL0.le _)

theorem giantCandidatePhysicalCellWidth_root_eventually (k : ℕ) (Cstep : ℝ) :
    ∀ᶠ x : ℝ in atTop,
      ((giantCandidatePhysicalCellWidth k Cstep x : ℝ) * (Real.exp (Real.sqrt (Real.log x)))^2)^
        ((giantTwoSidedSourceMomentLength x : ℝ)⁻¹) ≤ 2 := by
  let A := (k : ℝ)*giantCandidateGroupLogRate
  let B := max Cstep 0
  let C := Real.log 2 + B + A + 2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hA : 0 ≤ A := mul_nonneg (Nat.cast_nonneg _) (by unfold giantCandidateGroupLogRate; positivity)
  have hB : 0 ≤ B := le_max_right _ _
  have hlog := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1/2)).bound zero_lt_one
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ), Real.tendsto_log_atTop.eventually hlog,
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/50)).comp Real.tendsto_log_atTop).eventually_ge_atTop
      (C/(2*Real.log 2))] with x hL hlog hgrow
  let L := Real.log x
  let n := giantTwoSidedSourceMomentLength x
  let t := L^B * Real.exp (A*L^(46/100 : ℝ))
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hroot : Real.sqrt L = L^(1/2 : ℝ) := Real.sqrt_eq_rpow L
  have hlogL : Real.log L ≤ L^(1/2 : ℝ) := by
    change ‖Real.log L‖ ≤ (1 : ℝ)*‖L^(1/2 : ℝ)‖ at hlog
    rw [one_mul, Real.norm_of_nonneg (Real.rpow_nonneg hL0.le _)] at hlog
    exact (le_abs_self _).trans hlog
  have hsub : L^(46/100 : ℝ) ≤ L^(1/2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
  have hroot1 : 1 ≤ L^(1/2 : ℝ) := Real.one_le_rpow hL (by norm_num)
  have hC : C ≤ 2*Real.log 2*L^(1/50 : ℝ) := by
    change C/(2*Real.log 2) ≤ L^(1/50 : ℝ) at hgrow
    exact ((div_le_iff₀ (mul_pos zero_lt_two hlog2)).mp hgrow).trans_eq (mul_comm _ _)
  have hn : 2*L^(13/25 : ℝ) ≤ (n : ℝ) := by
    simpa only [n, giantTwoSidedSourceMomentLength, Nat.cast_mul, Nat.cast_ofNat] using
      (mul_le_mul_of_nonneg_left (Nat.le_ceil (L^(13/25 : ℝ))) zero_le_two)
  have he : Real.log 2 + B*Real.log L + A*L^(46/100 : ℝ) + 2*Real.sqrt L ≤ (n : ℝ)*Real.log 2 := by
    calc
      _ ≤ C*L^(1/2 : ℝ) := by
        rw [hroot]
        unfold C
        linarith only [mul_le_mul_of_nonneg_left hroot1 hlog2.le,
          mul_le_mul_of_nonneg_left hlogL hB, mul_le_mul_of_nonneg_left hsub hA]
      _ ≤ (2*Real.log 2*L^(1/50 : ℝ))*L^(1/2 : ℝ) :=
        mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hL0.le _)
      _ = Real.log 2*(2*L^(13/25 : ℝ)) := by
        rw [mul_assoc, ← Real.rpow_add hL0]
        norm_num
        ring
      _ ≤ _ := by rw [mul_comm (n : ℝ)]; exact mul_le_mul_of_nonneg_left hn hlog2.le
  have ht : 1 ≤ t := one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hL hB)
    (Real.one_le_exp (mul_nonneg hA (Real.rpow_nonneg hL0.le _)))
  have hwidth : (giantCandidatePhysicalCellWidth k Cstep x : ℝ) ≤ 2*t :=
    (Nat.ceil_lt_add_one (zero_le_one.trans ht)).le.trans (by linarith)
  have hexp : t = Real.exp (B*Real.log L + A*L^(46/100 : ℝ)) := by
    unfold t
    rw [Real.rpow_def_of_pos hL0, ← Real.exp_add, mul_comm (Real.log L) B]
  have hcost : (giantCandidatePhysicalCellWidth k Cstep x : ℝ)*(Real.exp (Real.sqrt L))^2 ≤ (2 : ℝ)^n := by
    calc
      _ ≤ 2*t*(Real.exp (Real.sqrt L))^2 := mul_le_mul_of_nonneg_right hwidth (sq_nonneg _)
      _ = Real.exp (Real.log 2 + B*Real.log L + A*L^(46/100 : ℝ) + 2*Real.sqrt L) := by
        calc
          _ = Real.exp (Real.log 2)*Real.exp (B*Real.log L + A*L^(46/100 : ℝ))*
                (Real.exp (Real.sqrt L)*Real.exp (Real.sqrt L)) := by rw [Real.exp_log zero_lt_two, ← pow_two, ← hexp]
          _ = _ := by simp only [← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp ((n : ℝ)*Real.log 2) := Real.exp_le_exp.mpr he
      _ = _ := by rw [Real.exp_nat_mul, Real.exp_log zero_lt_two]
  exact (Real.rpow_le_rpow (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) hcost
    (inv_nonneg.mpr (Nat.cast_nonneg n))).trans_eq
      (Real.pow_rpow_inv_natCast zero_le_two (giantTwoSidedSourceMomentLength_pos hL0).ne')

end
end ArtinMatthews
