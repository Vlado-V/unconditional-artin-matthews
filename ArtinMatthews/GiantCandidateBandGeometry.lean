module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt


set_option backward.privateInPublic true
@[expose] public section

/-! The candidate bands double their logarithmic height until the full
interval fits. The upper endpoint is open, so adjacent bands are disjoint
even when their common endpoint is a prime. -/
namespace ArtinMatthews
open Filter Finset
open scoped BigOperators
noncomputable section

def giantCandidateGroupCount (a b x : ℝ) : ℕ :=
  ⌊(b-a)*Real.log (Real.log x)/Real.log 2⌋₊

def giantCandidateGroupHeight (a x : ℝ) (k : ℕ) : ℝ :=
  (2:ℝ)^k * (Real.log x)^a

def giantCandidatePrimeInterval (y : ℝ) : Finset ℕ :=
  (Nat.primesLE ⌊Real.exp (2*y)⌋₊).filter
    (fun p => Real.exp y ≤ (p:ℝ) ∧ (p:ℝ) < Real.exp (2*y))

theorem mem_giantCandidatePrimeInterval {y : ℝ} {p : ℕ} :
    p ∈ giantCandidatePrimeInterval y ↔
      p.Prime ∧ Real.exp y ≤ (p:ℝ) ∧ (p:ℝ) < Real.exp (2*y) := by
  simp only [giantCandidatePrimeInterval,mem_filter,Nat.mem_primesLE]
  constructor
  · exact fun h => ⟨h.1.2,h.2⟩
  · rintro ⟨hp,hlo,hhi⟩
    exact ⟨⟨(Nat.le_floor_iff (Real.exp_nonneg _)).mpr hhi.le,hp⟩,hlo,hhi⟩

theorem giantCandidateGroupHeight_pos (a x : ℝ) (hx : 1 < x) (k : ℕ) :
    0 < giantCandidateGroupHeight a x k :=
  mul_pos (pow_pos (by norm_num) k) (Real.rpow_pos_of_pos (Real.log_pos hx) a)

theorem giantCandidateGroupHeight_ge (a x : ℝ) (hx : 1 < x) (k : ℕ) :
    (Real.log x)^a ≤ giantCandidateGroupHeight a x k := by
  unfold giantCandidateGroupHeight
  exact le_mul_of_one_le_left (Real.rpow_nonneg (Real.log_pos hx).le a)
    (one_le_pow₀ (by norm_num))

theorem giantCandidateGroupIndex_iff {a b x : ℝ} (hab : a ≤ b)
    (hx : 1 ≤ Real.log x) (k : ℕ) :
    k < giantCandidateGroupCount a b x ↔ 2 * giantCandidateGroupHeight a x k ≤ (Real.log x)^b := by
  have hL : 0 < Real.log x := zero_lt_one.trans_le hx
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hh : 0 < giantCandidateGroupHeight a x k :=
    mul_pos (pow_pos (by norm_num) k) (Real.rpow_pos_of_pos hL a)
  have hQ : 0 ≤ (b-a)*Real.log (Real.log x)/Real.log 2 :=
    div_nonneg (mul_nonneg (sub_nonneg.mpr hab) (Real.log_nonneg hx)) hlog2.le
  have hlogH : Real.log (2 * giantCandidateGroupHeight a x k) =
      ((k:ℝ)+1)*Real.log 2 + a*Real.log (Real.log x) := by
    rw [Real.log_mul (by norm_num) hh.ne',giantCandidateGroupHeight,
      Real.log_mul (pow_pos (by norm_num : (0:ℝ)<2) k).ne' (Real.rpow_pos_of_pos hL a).ne',
      Real.log_pow,Real.log_rpow hL]
    ring
  unfold giantCandidateGroupCount
  rw [← Nat.succ_le_iff,Nat.le_floor_iff hQ,Nat.cast_succ,le_div_iff₀ hlog2,
    ← Real.log_le_log_iff (mul_pos (by norm_num) hh) (Real.rpow_pos_of_pos hL b),
    hlogH,Real.log_rpow hL]
  constructor <;> intro h <;> nlinarith

theorem giantCandidateGroupHeight_two_le_of_lt {a x : ℝ} (hx : 1 < x)
    {k l : ℕ} (hkl : k < l) :
    2 * giantCandidateGroupHeight a x k ≤ giantCandidateGroupHeight a x l := by
  have h := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (Nat.succ_le_of_lt hkl)
  calc
    _ = (2:ℝ)^(k+1)*(Real.log x)^a := by
      unfold giantCandidateGroupHeight
      rw [pow_succ]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right h (Real.rpow_nonneg (Real.log_pos hx).le a)

theorem giantCandidatePrimeInterval_disjoint {y z : ℝ} (hyz : 2*y ≤ z) :
    Disjoint (giantCandidatePrimeInterval y) (giantCandidatePrimeInterval z) := by
  apply disjoint_left.mpr
  intro p hp hq
  exact (not_lt_of_ge ((Real.exp_le_exp.mpr hyz).trans
    (mem_giantCandidatePrimeInterval.mp hq).2.1)) (mem_giantCandidatePrimeInterval.mp hp).2.2

theorem giantCandidateGroupCount_bounds_eventually (a b : ℝ) (hab : a < b) :
    ∀ᶠ x : ℝ in atTop,
      ((b-a)/(2*Real.log 2))*Real.log (Real.log x) ≤ (giantCandidateGroupCount a b x:ℝ) ∧
        (giantCandidateGroupCount a b x:ℝ) ≤ ((b-a)/Real.log 2)*Real.log (Real.log x) := by
  let D := (b-a)/Real.log 2
  have hD : 0 < D := div_pos (sub_pos.mpr hab) (Real.log_pos (by norm_num))
  have hlog := (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually
    (eventually_ge_atTop (2/D))
  filter_upwards [hlog] with x hx
  change 2/D ≤ Real.log (Real.log x) at hx
  have htwo : 2 ≤ D*Real.log (Real.log x) := by
    simpa only [mul_comm] using (div_le_iff₀ hD).mp hx
  have heq : (b-a)*Real.log (Real.log x)/Real.log 2 = D*Real.log (Real.log x) := by
    unfold D
    ring
  have hhalfeq : (b-a)/(2*Real.log 2) = D/2 := by unfold D; ring
  unfold giantCandidateGroupCount
  rw [heq,hhalfeq]
  have hfloor := Nat.lt_floor_add_one (D*Real.log (Real.log x))
  exact ⟨by nlinarith, Nat.floor_le (by linarith)⟩

end
end ArtinMatthews
