module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Topology.ContinuousMap.Weierstrass
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Complex polynomial approximation on the real compact unit interval,
derived from the proved real Weierstrass theorem on both components. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace ArtinMatthews

theorem spectral_complex_polynomial_approximation (F : ℝ → ℂ)
    (hF : ContinuousOn F (Icc (0 : ℝ) 1)) (ε : ℝ) (hε : 0 < ε) :
    ∃ P : Polynomial ℂ, ∀ t ∈ Icc (0 : ℝ) 1, ‖P.eval (t : ℂ)-F t‖ < ε := by
  obtain ⟨p,hp⟩ := exists_polynomial_near_of_continuousOn 0 1 (fun t => (F t).re)
    (Complex.continuous_re.comp_continuousOn hF) (ε/2) (half_pos hε)
  obtain ⟨q,hq⟩ := exists_polynomial_near_of_continuousOn 0 1 (fun t => (F t).im)
    (Complex.continuous_im.comp_continuousOn hF) (ε/2) (half_pos hε)
  let P : Polynomial ℂ := p.map (algebraMap ℝ ℂ)+Polynomial.C Complex.I*q.map (algebraMap ℝ ℂ)
  have heval (t : ℝ) : P.eval (t : ℂ) = ((p.eval t : ℝ) : ℂ)+Complex.I*((q.eval t : ℝ) : ℂ) := by
    simp only [P,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C]
    rw [show (t : ℂ) = (algebraMap ℝ ℂ) t by rfl,Polynomial.eval_map_apply,Polynomial.eval_map_apply]
    rfl
  refine ⟨P,?_⟩
  intro t ht
  have heq : P.eval (t : ℂ)-F t =
      ((p.eval t-(F t).re : ℝ) : ℂ)+Complex.I*((q.eval t-(F t).im : ℝ) : ℂ) := by
    rw [heval]
    apply Complex.ext <;> simp
  rw [heq]
  calc
    _ ≤ ‖((p.eval t-(F t).re : ℝ) : ℂ)‖+‖Complex.I*((q.eval t-(F t).im : ℝ) : ℂ)‖ := norm_add_le _ _
    _ = |p.eval t-(F t).re|+|q.eval t-(F t).im| := by
      rw [norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs]
    _ < ε/2+ε/2 := add_lt_add (hp t ht) (hq t ht)
    _ = ε := add_halves ε

end ArtinMatthews
