module

public import ArtinMatthews.SourceContinuedPoissonRowKernel
public import ArtinMatthews.SourceContinuedPoissonRowStripBounds
public import ArtinMatthews.SourceRowEulerContourDomain
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! Exact no-pole shifts in each complex coordinate, at fixed other
heights, with the literal source Mellin weights and Gaussian. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators Set MeasureTheory Complex
open VaryingKummerAnalytic SourcePhysical
open scoped NumberField Classical BigOperators
noncomputable section
variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable {J : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F J) (hJ : J ≠ ⊥)
local notation "S" => sourceHilbertSet F S₀
local notation "R" => sourceRing F S₀
local notation "K" => sourceContinuedPoissonRowKernel F S₀ hζ η hJ
local notation "H" => sourceContourHeightWeight

theorem sourceContinuedPoissonRowKernel_shift_xi
    (hcut : principalAngularCutoff F J ⊆ S) (v : InfinitePlace F) (u : {a : R // a ≠ 0})
    (hu : ¬ ∃ a : F, a^6 = (u.val : F))
    {X Y Z : ℝ} (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) {a b : ℝ}
    (ha : 1 < a) (hab : a ≤ b) (w z : ℂ) (hw : 3/1000 ≤ w.re) (hz : 2/5 ≤ z.re) :
    (∫ t : ℝ, K v u X Y Z (sourcePoissonVertical a t,w,z)) = ∫ t : ℝ, K v u X Y Z (sourcePoissonVertical b t,w,z) := by
  obtain ⟨C, hC, h⟩ := exists_sourceContinuedPoissonRowKernel_right_strip_bound F S₀ hζ η hJ hcut v u hu
    hX hY hZ a b w.re z.re ha
  apply source_vertical_integral_eq_of_heightWeight (fun x => K v u X Y Z (x,w,z)) (C := C*(2*(1+z.im^2))) hab
  · apply sourceContinuedPoissonRowKernel_differentiableOn_path F S₀ hζ η hJ hcut v u hu hX hY hZ
      (p := fun x => (x,w,z)) (by fun_prop)
    · intro x hx
      exact sourceRowEulerOpenDomain_low_w_right F S₀ hζ η hJ u.val u.property (x,w,z)
        (ha.trans_le hx.1) hw hz
    · intro x _
      change 0 < z.re
      linarith
  · intro σ hσ t
    have h₀ := h σ hσ w.re ⟨hw,le_rfl⟩ z.re ⟨hz,le_rfl⟩ w.im z.im t
    have h₁ : ‖K v u X Y Z (sourcePoissonVertical σ t,w,z)‖ ≤
        C*(H w.im*H z.im)*Real.exp (-((t+z.im)^2)) := by
      simpa only [sourcePoissonVertical, Complex.re_add_im] using h₀
    have h₂ : H w.im*H z.im ≤ 1 :=
      (mul_le_of_le_one_left (sourceContourHeightWeight_nonneg z.im)
        (sourceContourHeightWeight_le_one w.im)).trans (sourceContourHeightWeight_le_one z.im)
    calc
      _ ≤ C*(H w.im*H z.im)*Real.exp (-((t+z.im)^2)) := h₁
      _ ≤ C*Real.exp (-((t+z.im)^2)) :=
        mul_le_mul_of_nonneg_right (mul_le_of_le_one_right hC.le h₂) (Real.exp_nonneg _)
      _ ≤ C*(2*(1+z.im^2)*H t) := mul_le_mul_of_nonneg_left (sourceGaussian_translate_le_heightWeight t z.im) hC.le
      _ = _ := by ring

theorem sourceContinuedPoissonRowKernel_shift_z
    (hcut : principalAngularCutoff F J ⊆ S) (v : InfinitePlace F) (u : {a : R // a ≠ 0})
    (hu : ¬ ∃ a : F, a^6 = (u.val : F))
    {X Y Z : ℝ} (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) {a b : ℝ}
    (ha : 2/5 ≤ a) (hab : a ≤ b) (ξ w : ℂ) (hξ : 1 < ξ.re) (hw : 3/1000 ≤ w.re) :
    (∫ t : ℝ, K v u X Y Z (ξ,w,sourcePoissonVertical a t)) = ∫ t : ℝ, K v u X Y Z (ξ,w,sourcePoissonVertical b t) := by
  obtain ⟨C, hC, h⟩ := exists_sourceContinuedPoissonRowKernel_right_strip_bound F S₀ hζ η hJ hcut v u hu
    hX hY hZ ξ.re ξ.re w.re b hξ
  apply source_vertical_integral_eq_of_heightWeight (fun x => K v u X Y Z (ξ,w,x)) (C := C) hab
  · apply sourceContinuedPoissonRowKernel_differentiableOn_path F S₀ hζ η hJ hcut v u hu hX hY hZ
      (p := fun x => (ξ,w,x)) (by fun_prop)
    · intro x hx
      exact sourceRowEulerOpenDomain_low_w_right F S₀ hζ η hJ u.val u.property (ξ,w,x) hξ hw (ha.trans hx.1)
    · intro x hx
      change 0 < x.re
      exact (by norm_num : (0:ℝ) < 2/5).trans_le (ha.trans hx.1)
  · intro σ hσ t
    have h₀ := h ξ.re ⟨le_rfl,le_rfl⟩ w.re ⟨hw,le_rfl⟩ σ ⟨ha.trans hσ.1,hσ.2⟩ w.im t ξ.im
    have h₁ : ‖K v u X Y Z (ξ,w,sourcePoissonVertical σ t)‖ ≤
        C*(H w.im*H t)*Real.exp (-((ξ.im+t)^2)) := by
      simpa only [sourcePoissonVertical, Complex.re_add_im] using h₀
    have hG : Real.exp (-((ξ.im+t)^2)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [sq_nonneg (ξ.im+t)])
    calc
      _ ≤ C*(H w.im*H t)*Real.exp (-((ξ.im+t)^2)) := h₁
      _ ≤ C*(H w.im*H t) := mul_le_of_le_one_right
        (mul_nonneg hC.le (mul_nonneg (sourceContourHeightWeight_nonneg w.im) (sourceContourHeightWeight_nonneg t))) hG
      _ ≤ C*H t := mul_le_mul_of_nonneg_left
        (mul_le_of_le_one_left (sourceContourHeightWeight_nonneg t) (sourceContourHeightWeight_le_one w.im)) hC.le

theorem sourceContinuedPoissonRowKernel_shift_w
    (hcut : principalAngularCutoff F J ⊆ S) (v : InfinitePlace F) (u : {a : R // a ≠ 0})
    (hu : ¬ ∃ a : F, a^6 = (u.val : F))
    {X Y Z : ℝ} (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) {a b : ℝ}
    (ha : 3/1000 ≤ a) (hab : a ≤ b) (ξ z : ℂ) (hξ : 1 < ξ.re) (hz : 2/5 ≤ z.re) :
    (∫ t : ℝ, K v u X Y Z (ξ,sourcePoissonVertical a t,z)) = ∫ t : ℝ, K v u X Y Z (ξ,sourcePoissonVertical b t,z) := by
  obtain ⟨C, hC, h⟩ := exists_sourceContinuedPoissonRowKernel_right_strip_bound F S₀ hζ η hJ hcut v u hu
    hX hY hZ ξ.re ξ.re b z.re hξ
  apply source_vertical_integral_eq_of_heightWeight (fun x => K v u X Y Z (ξ,x,z)) (C := C) hab
  · apply sourceContinuedPoissonRowKernel_differentiableOn_path F S₀ hζ η hJ hcut v u hu hX hY hZ
      (p := fun x => (ξ,x,z)) (by fun_prop)
    · intro x hx
      exact sourceRowEulerOpenDomain_low_w_right F S₀ hζ η hJ u.val u.property (ξ,x,z) hξ (ha.trans hx.1) hz
    · intro x _
      change 0 < z.re
      linarith
  · intro σ hσ t
    have h₀ := h ξ.re ⟨le_rfl,le_rfl⟩ σ ⟨ha.trans hσ.1,hσ.2⟩ z.re ⟨hz,le_rfl⟩ t z.im ξ.im
    have h₁ : ‖K v u X Y Z (ξ,sourcePoissonVertical σ t,z)‖ ≤
        C*(H t*H z.im)*Real.exp (-((ξ.im+z.im)^2)) := by
      simpa only [sourcePoissonVertical, Complex.re_add_im] using h₀
    have hG : Real.exp (-((ξ.im+z.im)^2)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [sq_nonneg (ξ.im+z.im)])
    calc
      _ ≤ C*(H t*H z.im)*Real.exp (-((ξ.im+z.im)^2)) := h₁
      _ ≤ C*(H t*H z.im) := mul_le_of_le_one_right
        (mul_nonneg hC.le (mul_nonneg (sourceContourHeightWeight_nonneg t) (sourceContourHeightWeight_nonneg z.im))) hG
      _ ≤ C*H t := mul_le_mul_of_nonneg_left
        (mul_le_of_le_one_right (sourceContourHeightWeight_nonneg t) (sourceContourHeightWeight_le_one z.im)) hC.le

end
end ArtinMatthews.SourceEulerAssembly
