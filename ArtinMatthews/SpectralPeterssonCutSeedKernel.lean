module

public import ArtinMatthews.SpectralPeterssonCutPeriodization
public import ArtinMatthews.SpectralPeterssonCutRadial
public import ArtinMatthews.SpectralPeterssonSeedProduct
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.Tactic.Basify
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! The original sharp-cut seed pairing separates into its exact
horizontal character and vertical Gamma density. -/
noncomputable section
open Set MeasureTheory UpperHalfPlane
open scoped ComplexConjugate

namespace ArtinMatthews

theorem spectralPeterssonStripCut_pair_coordinates (k : ℕ) (hk : 2 ≤ k)
    (m n : ℕ+) (A : ℝ) (z : UpperHalfPlane) :
    UpperHalfPlane.petersson (k : ℤ) (spectralPeterssonStripCutSeed m A)
      (spectralPeterssonStripCutSeed n A) z =
      (Ioc (0 : ℝ) 1).indicator (fun x => atkinPhase (((n : ℝ)-(m : ℝ))*x)) z.re *
        (z.im^2*spectralPeterssonCutPairRadial k m n A z.im : ℝ) := by
  have hstrip : z ∈ hyperbolicCuspStrip 1 0 ↔ z.re ∈ Ioc (0 : ℝ) 1 := by
    change (z.re ∈ Ioc (0 : ℝ) 1 ∧ 0 < z.im) ↔ _
    simp only [z.im_pos,and_true]
  simp only [UpperHalfPlane.petersson,zpow_natCast]
  by_cases hx : z.re ∈ Ioc (0 : ℝ) 1
  · have hz := hstrip.mpr hx
    simp only [spectralPeterssonStripCutSeed,indicator_of_mem hz,indicator_of_mem hx]
    by_cases hm : A < 4*Real.pi*(m : ℝ)*z.im
    · by_cases hn : A < 4*Real.pi*(n : ℝ)*z.im
      · simp only [spectralPeterssonHeightCutSeed,if_pos hm,if_pos hn]
        rw [spectralHolomorphicCuspSeed_pair]
        rw [spectralPeterssonCutPairRadial,if_pos ⟨hm,hn⟩]
        have hpow : z.im^2*z.im^(k-2) = z.im^k := by
          rw [← pow_add]
          congr 1
          omega
        have hreal : z.im^2*(z.im^(k-2)*Real.exp (-(2*Real.pi*((m : ℝ)+(n : ℝ))*z.im))) =
            Real.exp (-(2*Real.pi*((m : ℝ)+(n : ℝ))*z.im))*z.im^k := by
          rw [← mul_assoc,hpow]
          ring
        rw [hreal]
        push_cast
        ring
      · simp [spectralPeterssonHeightCutSeed,hm,hn,spectralPeterssonCutPairRadial]
    · simp [spectralPeterssonHeightCutSeed,hm,spectralPeterssonCutPairRadial]
  · have hz : z ∉ hyperbolicCuspStrip 1 0 := fun h => hx (hstrip.mp h)
    simp only [spectralPeterssonStripCutSeed,indicator_of_notMem hz,indicator_of_notMem hx,
      UpperHalfPlane.petersson,map_zero,zero_mul]

end ArtinMatthews
