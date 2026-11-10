module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import ArtinMatthews.VaryingKummerAnalyticConductorConvexity
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Apply the proved strip maximum to an affine rescaling. The earlier
strip ending at 5/4 gives the conductor-norm exponent 0.6235 at Re(w)=.003;
the actual source estimate needs a bound by the one-half power. -/
namespace ArtinMatthews.SourceEulerAssembly
open Complex VaryingKummerAnalytic
noncomputable section

theorem sourceNarrowStripConvexity {f : ℂ → ℂ} {A C : ℝ} (hA : 0 < A) (hC : 0 < C)
    (m : ℕ) (hf : Differentiable ℂ f)
    (hleft : ∀ t : ℝ, ‖f ((-1/1000 : ℂ)+(t : ℂ)*I)‖ ≤ C*A^(501/500 : ℝ)*(|t|+2)^m)
    (hright : ∀ t : ℝ, ‖f ((1001/1000 : ℂ)+(t : ℂ)*I)‖ ≤ C*(|t|+2)^m)
    (hg : ∃ E D R : ℝ, 0 < E ∧ 0 < D ∧ ∀ σ : ℝ,
      -(1/4 : ℝ) ≤ σ → σ ≤ 5/4 → ∀ t : ℝ, R ≤ |t| →
      ‖f ((σ : ℂ)+(t : ℂ)*I)‖ ≤ E*Real.exp (D*(|t|+2)^2))
    {s : ℂ} (hsa : -(1/1000 : ℝ) ≤ s.re) (hsb : s.re ≤ 1001/1000) :
    ‖f s‖ ≤ (C*6^m*(250/167)^m)*A^(1001/1000-s.re)*(|s.im|+2)^m := by
  let a : ℝ := 167/250
  let b : ℝ := 83/500
  let G : ℂ → ℂ := fun z => f ((a : ℂ)*z+(b : ℂ))
  have ha : 0 < a := by norm_num [a]
  have ha₁ : a ≤ 1 := by norm_num [a]
  have hG : Differentiable ℂ G := hf.comp (by fun_prop)
  have hscale (t : ℝ) : |a*t| ≤ |t| := by
    rw [abs_mul, abs_of_pos ha]
    exact mul_le_of_le_one_left (abs_nonneg _) ha₁
  have himage (x t : ℝ) : (a : ℂ)*((x : ℂ)+(t : ℂ)*I)+(b : ℂ) =
      ((a*x+b : ℝ) : ℂ)+((a*t : ℝ) : ℂ)*I := by
    push_cast
    ring
  have haim : a*(-1/4)+b = (-1/1000 : ℝ) := by norm_num [a,b]
  have hbim : a*(5/4)+b = (1001/1000 : ℝ) := by norm_num [a,b]
  have haim' : (((a*(-1/4)+b : ℝ)) : ℂ) = (-1/1000 : ℂ) := by rw [haim]; norm_num
  have hbim' : (((a*(5/4)+b : ℝ)) : ℂ) = (1001/1000 : ℂ) := by rw [hbim]; norm_num
  have hGl (t : ℝ) : ‖G ((-1/4 : ℂ)+(t : ℂ)*I)‖ ≤ C*(A^a)^(3/2 : ℝ)*(|t|+2)^m := by
    have h : (A^a)^(3/2 : ℝ) = A^(501/500 : ℝ) := by
      rw [← Real.rpow_mul hA.le]
      congr 1
      norm_num [a]
    have hm := himage (-1/4) t
    push_cast at hm
    have hm' : (a : ℂ)*((-1/4 : ℂ)+(t : ℂ)*I)+(b : ℂ) =
        (-1/1000 : ℂ)+((a*t : ℝ) : ℂ)*I := by
      exact hm.trans (by push_cast at haim'; rw [haim']; push_cast; rfl)
    change ‖f ((a : ℂ)*((-1/4 : ℂ)+(t : ℂ)*I)+(b : ℂ))‖ ≤ _
    rw [hm', h]
    exact (hleft (a*t)).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (show |a*t|+2 ≤ |t|+2 by linarith only [hscale t]) m) (by positivity))
  have hGr (t : ℝ) : ‖G ((5/4 : ℂ)+(t : ℂ)*I)‖ ≤ C*(|t|+2)^m := by
    have hm := himage (5/4) t
    push_cast at hm
    have hm' : (a : ℂ)*((5/4 : ℂ)+(t : ℂ)*I)+(b : ℂ) =
        (1001/1000 : ℂ)+((a*t : ℝ) : ℂ)*I := by
      exact hm.trans (by push_cast at hbim'; rw [hbim']; push_cast; rfl)
    change ‖f ((a : ℂ)*((5/4 : ℂ)+(t : ℂ)*I)+(b : ℂ))‖ ≤ _
    rw [hm']
    exact (hright (a*t)).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (show |a*t|+2 ≤ |t|+2 by linarith only [hscale t]) m) hC.le)
  have hGg : ∃ E D R : ℝ, 0 < E ∧ 0 < D ∧ ∀ σ : ℝ,
      -(1/4 : ℝ) ≤ σ → σ ≤ 5/4 → ∀ t : ℝ, R ≤ |t| →
      ‖G ((σ : ℂ)+(t : ℂ)*I)‖ ≤ E*Real.exp (D*(|t|+2)^2) := by
    obtain ⟨E,D,R,hE,hD,hf⟩ := hg
    refine ⟨E,D,R/a,hE,hD,?_⟩
    intro σ hσ hσ' t ht
    have hla := mul_le_mul_of_nonneg_left hσ ha.le
    have hra := mul_le_mul_of_nonneg_left hσ' ha.le
    have hl : -(1/4 : ℝ) ≤ a*σ+b := by linarith [haim, hla]
    have hr : a*σ+b ≤ (5/4 : ℝ) := by linarith [hbim, hra]
    have hT : R ≤ |a*t| := by
      rw [abs_mul, abs_of_pos ha, mul_comm]
      exact (div_le_iff₀ ha).mp ht
    change ‖f ((a : ℂ)*((σ : ℂ)+(t : ℂ)*I)+(b : ℂ))‖ ≤ _
    rw [himage]
    apply (hf (a*σ+b) hl hr (a*t) hT).trans
    apply mul_le_mul_of_nonneg_left _ hE.le
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (show |a*t|+2 ≤ |t|+2 by linarith only [hscale t]) 2) hD.le
  let z : ℂ := (s-(b : ℂ))/(a : ℂ)
  have hzre : z.re = (s.re-b)/a := by simp [z]
  have hzim : z.im = s.im/a := by simp [z]
  have hza : -(1/4 : ℝ) ≤ z.re := by
    rw [hzre, le_div_iff₀ ha]
    linarith [haim]
  have hzb : z.re ≤ (5/4 : ℝ) := by
    rw [hzre, div_le_iff₀ ha]
    linarith [hbim]
  have H := conductor_strip_convexity (Real.rpow_pos_of_pos hA a) hC m hG hGl hGr hGg hza hzb
  have hGz : G z = f s := by
    change f ((a : ℂ)*((s-(b : ℂ))/(a : ℂ))+(b : ℂ)) = f s
    congr 1
    field_simp [Complex.ofReal_ne_zero.mpr ha.ne']
    ring
  have hp : (A^a)^(5/4-z.re) = A^(1001/1000-s.re) := by
    rw [← Real.rpow_mul hA.le, hzre]
    congr 1
    dsimp [a,b]
    ring
  have hheight : |z.im|+2 ≤ (250/167)*(|s.im|+2) := by
    rw [hzim, abs_div, abs_of_pos ha]
    dsimp [a]
    linarith
  rw [hGz, hp] at H
  calc
    _ ≤ (C*6^m)*A^(1001/1000-s.re)*((250/167)*(|s.im|+2))^m := by
      exact H.trans (by gcongr)
    _ = _ := by rw [mul_pow]; ring

end
end ArtinMatthews.SourceEulerAssembly
