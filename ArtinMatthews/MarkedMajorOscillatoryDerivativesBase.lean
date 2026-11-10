module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

/-! Elementary compact derivative bounds and the actual unit-modulus oscillator. -/

namespace ArtinMatthews
noncomputable section
open Set
open scoped ContDiff BigOperators

def markedRealOscillator (t : ℝ) : ℂ := Complex.exp (Complex.I * (t : ℂ))

theorem markedRealOscillator_contDiff : ContDiff ℝ ∞ markedRealOscillator :=
  (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp

theorem markedRealOscillator_iteratedDeriv (n : ℕ) :
    iteratedDeriv n markedRealOscillator =
      fun t => Complex.I ^ n * markedRealOscillator t := by
  induction n with
  | zero => ext t; simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    have hd : HasDerivAt markedRealOscillator
        (markedRealOscillator t * Complex.I) t := by
      simpa only [markedRealOscillator, id_eq, Complex.ofReal_one, mul_one] using!
        (((hasDerivAt_id t).ofReal_comp).const_mul Complex.I).cexp
    convert (hd.const_mul (Complex.I ^ n)).deriv using 1
    rw [pow_succ]
    ring

theorem markedRealOscillator_norm_iteratedFDeriv (n : ℕ) (t : ℝ) :
    ‖iteratedFDeriv ℝ n markedRealOscillator t‖ = 1 := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    congrFun (markedRealOscillator_iteratedDeriv n) t, norm_mul, norm_pow,
    Complex.norm_I, one_pow, one_mul]
  simp only [markedRealOscillator, Complex.norm_exp, Complex.mul_re, Complex.I_re,
    Complex.ofReal_re, Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero,
    sub_self, Real.exp_zero]

/-- Smoothness on an actual compact set supplies a common bound for every
derivative up to a prescribed finite order. -/
theorem compact_norm_iteratedFDeriv_bound
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (hf : ContDiff ℝ ∞ f) (K : Set E) (hK : IsCompact K) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ i ≤ n, ∀ x ∈ K, ‖iteratedFDeriv ℝ i f x‖ ≤ C := by
  let G : E → ℝ := fun x => ∑ i ∈ Finset.range (n + 1), ‖iteratedFDeriv ℝ i f x‖
  have hG : Continuous G :=
    continuous_finsetSum _ (fun i _ => (hf.continuous_iteratedFDeriv (by simp)).norm)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hG.continuousOn
  refine ⟨|M| + 1, by positivity, fun i hi x hx => ?_⟩
  calc
    ‖iteratedFDeriv ℝ i f x‖ ≤ G x := by
      change ‖iteratedFDeriv ℝ i f x‖ ≤
        ∑ j ∈ Finset.range (n + 1), ‖iteratedFDeriv ℝ j f x‖
      exact Finset.single_le_sum (f := fun j : ℕ => ‖iteratedFDeriv ℝ j f x‖)
        (fun _ _ => norm_nonneg _)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
    _ ≤ ‖G x‖ := le_abs_self _
    _ ≤ M := hM x hx
    _ ≤ |M| + 1 := by linarith [le_abs_self M]

end
end ArtinMatthews
