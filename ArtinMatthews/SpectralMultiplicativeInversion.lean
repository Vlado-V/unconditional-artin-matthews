module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Exact inversion of the positive multiplicative Haar measure, with
integrability transported by the genuine Mellin change of variables. -/

noncomputable section
open Set MeasureTheory

namespace ArtinMatthews

theorem spectral_multiplicative_inverse_integral (F : ℝ → ℂ) {a : ℝ} (ha : 0 < a) :
    (∫ u in Ioi (0 : ℝ), F (a/u)/(u : ℂ)) = ∫ r in Ioi (0 : ℝ), F r/(r : ℂ) := by
  have h := mellin_comp_inv (fun u : ℝ => F (a*u)) (0 : ℂ)
  rw [neg_zero,mellin_comp_mul_left F 0 ha] at h
  simp only [neg_zero,Complex.cpow_zero,mellin,zero_sub,Complex.cpow_neg_one,smul_eq_mul,one_mul] at h
  convert h using 1
  · apply setIntegral_congr_fun measurableSet_Ioi
    intro u _
    dsimp only
    simp only [div_eq_mul_inv]
    ring
  · apply setIntegral_congr_fun measurableSet_Ioi
    intro r _
    dsimp only
    simp only [div_eq_mul_inv]
    ring

theorem spectral_multiplicative_inverse_integrable (F : ℝ → ℂ) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun u : ℝ => F (a/u)/(u : ℂ)) (Ioi (0 : ℝ)) ↔
      IntegrableOn (fun r : ℝ => F r/(r : ℂ)) (Ioi (0 : ℝ)) := by
  have hi : MellinConvergent (fun u : ℝ => (fun r : ℝ => F (a*r)) (u^(-1 : ℝ))) 0 ↔
      MellinConvergent (fun r : ℝ => F (a*r)) 0 := by
    simpa only [zero_div] using
      (MellinConvergent.comp_rpow (f := fun r : ℝ => F (a*r)) (s := 0) (a := (-1 : ℝ)) (by norm_num))
  have h := hi.trans (MellinConvergent.comp_mul_left (f := F) (s := 0) ha)
  simp only [MellinConvergent,zero_sub,Complex.cpow_neg_one,smul_eq_mul,Real.rpow_neg_one] at h
  convert h using 1
  · exact integrableOn_congr_fun (fun u _ => by simp only [div_eq_mul_inv,mul_comm]) measurableSet_Ioi
  · exact integrableOn_congr_fun (fun r _ => by simp only [div_eq_mul_inv,mul_comm]) measurableSet_Ioi

end ArtinMatthews
