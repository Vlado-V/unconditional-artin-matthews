module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

/-! The restricted coordinate costs L^.9 choices and saves one full
dyadic logarithm. The resulting scalar error is x L^(-1.1). -/

namespace ArtinMatthews
noncomputable section
open Filter
open scoped Asymptotics Topology

theorem giantCandidateDyadLogBudget (j : ℕ) (hj : 2 ≤ j)
    {L x N K I U D E A B T : ℝ} (hL : 0 < L)
    (hN : 0 ≤ N) (hK : 0 ≤ K) (hI : 0 ≤ I)
    (hU : 0 ≤ U) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hNbound : N ≤ T*x) (hKbound : K ≤ A*L) (hIbound : I ≤ B*L^(9/10:ℝ)) :
    2*N*(U/L)^(j-1)*((D*L^(-(1/10:ℝ))/L)*K^(j-1)+(E/L)*I*K^(j-2)) ≤
      (2*T*U^(j-1)*(D*A^(j-1)+E*B*A^(j-2)))*(x*L^(-(1/10:ℝ))/L) := by
  have hTL : 0 ≤ T*x := hN.trans hNbound
  have hAL : 0 ≤ A*L := hK.trans hKbound
  have hBL : 0 ≤ B*L^(9/10:ℝ) := hI.trans hIbound
  have hpow : L^(9/10:ℝ) = L*L^(-(1/10:ℝ)) := by
    calc
      _ = L^((1:ℝ)+(-(1/10:ℝ))) := by norm_num
      _ = _ := by rw [Real.rpow_add hL,Real.rpow_one]
  calc
    _ ≤ 2*(T*x)*(U/L)^(j-1)*
      ((D*L^(-(1/10:ℝ))/L)*(A*L)^(j-1)+(E/L)*(B*L^(9/10:ℝ))*(A*L)^(j-2)) := by
      gcongr
    _ = _ := by
      rw [hpow,show j-1=(j-2)+1 by omega]
      simp only [div_pow,mul_pow,pow_succ]
      field_simp [hL.ne',pow_ne_zero _ hL.ne']

theorem giantCandidateLogTenth_isLittleO :
    (fun x : ℝ => x*(Real.log x)^(-(1/10:ℝ))/Real.log x) =o[atTop]
      (fun x : ℝ => x/Real.log x) := by
  apply Asymptotics.isLittleO_of_tendsto'
  · filter_upwards [eventually_gt_atTop (1:ℝ)] with x hx
    exact fun h => (div_pos (zero_lt_one.trans hx) (Real.log_pos hx)).ne' h |>.elim
  · have hlim := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/10)).comp Real.tendsto_log_atTop
    apply hlim.congr'
    filter_upwards [eventually_gt_atTop (1:ℝ)] with x hx
    have hx₀ := zero_lt_one.trans hx
    have hL := Real.log_pos hx
    change (Real.log x)^(-(1/10:ℝ)) = (x*(Real.log x)^(-(1/10:ℝ))/Real.log x)/(x/Real.log x)
    field_simp [hx₀.ne',hL.ne']

end
end ArtinMatthews
