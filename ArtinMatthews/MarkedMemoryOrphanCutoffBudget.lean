module

public import ArtinMatthews.MarkedMinorArcProductMassActual
public import ArtinMatthews.MarkedMinorArcDirtyScalar


set_option backward.privateInPublic true
@[expose] public section

/-! The original logarithmic memory cutoff leaves at least half its
capacity for orphan identities after all actual active occurrences have
been counted. No prime-band cardinality is used in this budget. -/
namespace ArtinMatthews
noncomputable section
open Filter
open scoped Topology

theorem markedMemoryOrphan_active_budget (K : ℕ) :
    ∀ᶠ x : ℝ in atTop,
      K*((markedMemoryMomentLength x+1)*markedPadSlots x)+markedDirtyMemoryCutoff x/2 ≤
        markedDirtyMemoryCutoff x := by
  have ht := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<5/4)).comp Real.tendsto_log_atTop
  filter_upwards [ht.eventually (eventually_ge_atTop (16*(K:ℝ))),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with x hx hlog
  change 16*(K:ℝ)≤(Real.log x)^(5/4:ℝ) at hx
  have hL : 0<Real.log x := by linarith
  have hs : 1≤(Real.log x)^(1/2:ℝ) := Real.one_le_rpow hlog (by norm_num)
  have hq : 1≤(Real.log x)^(1/4:ℝ) := Real.one_le_rpow hlog (by norm_num)
  have hceil := Nat.ceil_lt_add_one (div_nonneg
    (Real.rpow_nonneg hL.le (1/2:ℝ)) (by norm_num : (0:ℝ)≤2))
  have hN : (markedMemoryMomentLength x:ℝ)+1≤4*(Real.log x)^(1/2:ℝ) := by
    unfold markedMemoryMomentLength
    push_cast
    linarith
  have hfloor := Nat.floor_le (Real.rpow_nonneg hL.le (1/100:ℝ))
  have hp : (Real.log x)^(1/100:ℝ)≤(Real.log x)^(1/4:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hlog (by norm_num)
  have hM : (markedPadSlots x:ℝ)≤2*(Real.log x)^(1/4:ℝ) := by
    unfold markedPadSlots
    push_cast
    linarith
  have hprod : ((markedMemoryMomentLength x:ℝ)+1)*(markedPadSlots x:ℝ)≤
      8*(Real.log x)^(3/4:ℝ) := by
    calc
      _ ≤ (4*(Real.log x)^(1/2:ℝ))*(2*(Real.log x)^(1/4:ℝ)) :=
        mul_le_mul hN hM (Nat.cast_nonneg _) (by positivity)
      _ = _ := by
        have he : (Real.log x)^(1/2:ℝ)*(Real.log x)^(1/4:ℝ)=(Real.log x)^(3/4:ℝ) := by
          rw [← Real.rpow_add hL]
          norm_num
        nlinarith
  have hbudget : (2*K*((markedMemoryMomentLength x+1)*markedPadSlots x):ℕ)≤markedDirtyMemoryCutoff x := by
    have hr : (2*(K:ℝ))*(((markedMemoryMomentLength x:ℝ)+1)*(markedPadSlots x:ℝ))≤
        (markedDirtyMemoryCutoff x:ℝ) := by
      calc
        _ ≤ 16*(K:ℝ)*(Real.log x)^(3/4:ℝ) := by
          have hh := mul_le_mul_of_nonneg_left hprod
            (mul_nonneg (by norm_num : (0:ℝ)≤2) (Nat.cast_nonneg K))
          nlinarith
        _ ≤ (Real.log x)^(3/4:ℝ)*(Real.log x)^(5/4:ℝ) := by
          have hh := mul_le_mul_of_nonneg_left hx (Real.rpow_nonneg hL.le (3/4:ℝ))
          nlinarith
        _ = (Real.log x)^2 := by
          rw [← Real.rpow_add hL]
          norm_num [Real.rpow_two]
        _ ≤ _ := Nat.le_ceil _
    exact_mod_cast hr
  have hh : 2*(K*((markedMemoryMomentLength x+1)*markedPadSlots x))≤markedDirtyMemoryCutoff x := by
    simpa only [Nat.mul_assoc] using hbudget
  omega

end
end ArtinMatthews
