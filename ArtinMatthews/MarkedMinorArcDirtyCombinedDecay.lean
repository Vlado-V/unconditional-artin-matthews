module

public import ArtinMatthews.MarkedMinorArcDirtyMajorDecay
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
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

/-! Numerical absorption of the actual delta-plus-major row envelope. -/
namespace ArtinMatthews
noncomputable section
open Filter
open scoped Topology

def markedDirtyCombinedEnvelope (D M : ℝ) (K : ℕ) (A₀ x : ℝ) : ℝ :=
  markedDirtyScalarEpsilon D K x+markedDirtyMajorEnvelope M K A₀ x

theorem markedDirtyCombinedEnvelope_log_tendsto {D M : ℝ} (hD : 0 ≤ D) (hM : 0 ≤ M)
    (K : ℕ) (A₀ A : ℝ) (hK : 100*(A+2)<(K:ℝ)) :
    Tendsto (fun x : ℝ => (Real.log x)^A*markedDirtyCombinedEnvelope D M K A₀ x)
      atTop (nhds 0) := by
  have hh := (markedDirtyScalar_log_tendsto hD K A hK).add
    (markedDirtyMajorEnvelope_log_tendsto hM K A₀ A)
  simpa only [markedDirtyCombinedEnvelope,mul_add,zero_add] using hh

theorem markedDirtyCombinedEnvelope_eventually_le {D M : ℝ} (hD : 0 ≤ D) (hM : 0 ≤ M)
    (K : ℕ) (A₀ A : ℝ) (hK : 100*(A+2)<(K:ℝ)) :
    ∀ᶠ x : ℝ in atTop,markedDirtyCombinedEnvelope D M K A₀ x ≤ (Real.log x)^(-A) := by
  have ht := markedDirtyCombinedEnvelope_log_tendsto hD hM K A₀ A hK
  filter_upwards [ht.eventually (gt_mem_nhds (show (0:ℝ)<1 by norm_num)),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with x hx hlog
  have hL : 0 < Real.log x := zero_lt_one.trans_le hlog
  have hp : 0 < (Real.log x)^A := Real.rpow_pos_of_pos hL _
  have hh : markedDirtyCombinedEnvelope D M K A₀ x ≤ 1/((Real.log x)^A) :=
    (le_div_iff₀ hp).mpr (by simpa only [mul_comm] using hx.le)
  simpa only [Real.rpow_neg hL.le,one_div] using hh

def markedDirtySufficientGroups (A : ℝ) : ℕ := ⌈100*(A+3)⌉₊

theorem markedDirtySufficientGroups_spec (A : ℝ) :
    100*(A+2)<(markedDirtySufficientGroups A:ℝ) := by
  have hh : 100*(A+3) ≤ (markedDirtySufficientGroups A:ℝ) := Nat.le_ceil _
  linarith

end
end ArtinMatthews
