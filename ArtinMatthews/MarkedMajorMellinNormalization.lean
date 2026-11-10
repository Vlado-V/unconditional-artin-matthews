module

public import ArtinMatthews.MarkedMajorMellinEndpointSum
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

namespace ArtinMatthews
open Finset MeasureTheory Complex
noncomputable section

theorem markedMajor_log_phase_div {w Z : ℝ} (hw : 0 < w) (hZ : 0 < Z) (t : ℝ) :
    Complex.exp (I*(t : ℂ)*(Real.log (w/Z) : ℂ)) =
      Complex.exp (-(I*(t : ℂ)*(Real.log Z : ℂ)))*Complex.exp (I*(t : ℂ)*(Real.log w : ℂ)) := by
  rw [Real.log_div hw.ne' hZ.ne',← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem markedMajorEndpointPolynomial_scale {α : Type*} (S : Finset α) (A : α → ℂ)
    (w : α → ℝ) (hw : ∀ i ∈ S, 0 < w i) {Z : ℝ} (hZ : 0 < Z) (t : ℝ) :
    markedMajorEndpointPolynomial S A (fun i => w i/Z) t =
      Complex.exp (-(I*(t : ℂ)*(Real.log Z : ℂ)))*markedMajorEndpointPolynomial S A w t := by
  unfold markedMajorEndpointPolynomial
  rw [mul_sum]
  apply sum_congr rfl
  intro i hi
  rw [markedMajor_log_phase_div (hw i hi) hZ]
  ring

theorem markedMajorEndpointPolynomial_product_scale {α β : Type*} (S : Finset α) (T : Finset β)
    (A : α → ℂ) (B : β → ℂ) (w : α → ℝ) (w' : β → ℝ)
    (hw : ∀ i ∈ S, 0 < w i) (hw' : ∀ j ∈ T, 0 < w' j)
    {Z : ℝ} (hZ : 0 < Z) (t s : ℝ) :
    markedMajorEndpointPolynomial S A (fun i => w i/Z) t *
      markedMajorEndpointPolynomial T B (fun j => w' j/Z) (s-t) =
      Complex.exp (-(I*(s : ℂ)*(Real.log Z : ℂ))) *
        (markedMajorEndpointPolynomial S A w t*markedMajorEndpointPolynomial T B w' (s-t)) := by
  rw [markedMajorEndpointPolynomial_scale S A w hw hZ,
    markedMajorEndpointPolynomial_scale T B w' hw' hZ]
  calc
    _ = (Complex.exp (-(I*(t : ℂ)*(Real.log Z : ℂ))) *
        Complex.exp (-(I*((s-t : ℝ) : ℂ)*(Real.log Z : ℂ)))) *
        (markedMajorEndpointPolynomial S A w t*markedMajorEndpointPolynomial T B w' (s-t)) := by ring
    _ = _ := by
      rw [← Complex.exp_add]
      congr 2
      push_cast
      ring

theorem markedMajor_scale_phase_norm (Z s : ℝ) :
    ‖Complex.exp (-(I*(s : ℂ)*(Real.log Z : ℂ)))‖ = 1 := by
  rw [Complex.norm_exp]
  simp

theorem markedMajor_XY_normalization {X Y : ℝ} (hX : X ≠ 0) (hY : Y ≠ 0) :
    ((Y*X : ℝ) : ℂ)^2 * (X : ℂ)⁻¹ * (Y : ℂ)⁻¹ = ((Y*X : ℝ) : ℂ) := by
  have hx : (X : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hX
  have hy : (Y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hY
  push_cast
  field_simp

end
end ArtinMatthews
