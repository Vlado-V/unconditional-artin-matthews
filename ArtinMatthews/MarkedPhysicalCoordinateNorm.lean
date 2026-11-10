module

public import ArtinMatthews.MarkedPhysicalCoordinateKernel
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

/-! Uniform bounds for the literal fixed-coordinate complex kernel.
The original V factors and all label guards remain in the coefficient. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem markedPhysicalCoordinateKernel_norm_le
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (V : J → ℝ) (pads : ℕ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q H W : ℝ) (hY : 0 < Y) (hQ : 0 ≤ Q) (hH : 0 ≤ H) (hW : 0 ≤ W)
    (hη : ∀ t,‖η t‖ ≤ H) (hψ : ∀ t,‖ψ t‖ ≤ W)
    (source target : MarkedRawActive P (pads+1)) (z z' : ℤ × ℤ) :
    ‖markedPhysicalCoordinateKernel V pads ψ η d₀ Y Q source target z z'‖ ≤
      |∏ j,(V j)⁻¹| * H^2*W*(1+4*Q^3/Y) := by
  have hD : 0 < (markedRawCopiedProduct ((markedRawActiveSplit pads) source).1:ℝ) := by
    exact_mod_cast markedRawCopiedProduct_pos ((markedRawActiveSplit pads) source).1
  have hk (b a l : ℤ) : ‖markedBanEdgeKernel ψ Q Y b a l‖ ≤ W*(1+4*Q^3/Y) := by
    apply (markedBanEdgeKernel_norm_le ψ hQ hY hW hψ b a l).trans
    apply mul_le_mul_of_nonneg_left _ hW
    split_ifs <;> linarith
  dsimp only [markedPhysicalCoordinateKernel]
  split_ifs with hprefix hdyad hdiv hban <;>
    try simp only [mul_zero,norm_zero] <;> try positivity
  have hd0 : 0 ≤ d₀ := by linarith [hdyad.2]
  have hr0 : 0 ≤ d₀/(markedRawCopiedProduct ((markedRawActiveSplit pads) source).1:ℝ) := div_nonneg hd0 hD.le
  have hr1 : d₀/(markedRawCopiedProduct ((markedRawActiveSplit pads) source).1:ℝ) ≤ 1 :=
    (div_le_one hD).mpr hdyad.1
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr0]
  calc
    _ ≤ |∏ j,(V j)⁻¹| * (1*H*H*(W*(1+4*Q^3/Y))) := by
      gcongr
      · exact hη _
      · exact hη _
      · exact hk _ _ _
    _ = _ := by ring

theorem markedPhysicalCoordinateKernel_atom_bound
    {J : Type*} [Fintype J] (V : J → ℝ) {v₀ : ℝ} (hv0 : 0 < v₀) (hV : ∀ j,v₀ ≤ V j) :
    |∏ j,(V j)⁻¹| ≤ (v₀⁻¹)^(Fintype.card J) := by
  rw [abs_of_nonneg (Finset.prod_nonneg (fun j _ => inv_nonneg.mpr (hv0.le.trans (hV j))))]
  calc
    _ ≤ ∏ _j : J,v₀⁻¹ := Finset.prod_le_prod₀ (fun _ _ => inv_nonneg.mpr (hv0.le.trans (hV _)))
      (fun j _ => inv_anti₀ hv0 (hV j))
    _ = _ := by simp

end ArtinMatthews
