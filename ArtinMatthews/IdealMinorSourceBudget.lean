module

public import ArtinMatthews.MarkedMinorArcGram
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import ArtinMatthews.IdealMinorGramBudget
public import ArtinMatthews.MarkedBonferroniTail
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Polynomial rational cutoffs dominate the actual normalized Gram
budget throughout the source's exponentially large product dyads. -/
namespace ArtinMatthews
open Filter
open scoped Topology
noncomputable section

def idealMinorCutoffExponent (E κ d : ℝ) : ℝ := 2*E+2*κ+d+12

theorem idealMinorGramBudget_source (c d E κ : ℝ) (hc : 0 < c) (hd : 0 ≤ d) :
    ∀ᶠ L : ℝ in atTop, ∀ U V r : ℕ, 0 < U → 0 < V → 0 < r →
      Real.exp (L^c)/4 ≤ (U : ℝ) → Real.exp (L^c)/4 ≤ (V : ℝ) →
      L^(idealMinorCutoffExponent E κ d)/2 ≤ (r : ℝ) →
      (r : ℝ) ≤ (U : ℝ)*(V : ℝ)/L^(idealMinorCutoffExponent E κ d) →
      1+Real.log (2*(r : ℝ)) ≤ L^(d+3) →
      64*L^(2*κ)*(markedMinorGramBudget U V r/((U : ℝ)*(V : ℝ))) ≤ L^(-2*E) := by
  let a := idealMinorCutoffExponent E κ d
  have hfast := (rpow_mul_exp_neg_rpow_tendsto a hc (by norm_num : (0 : ℝ) < 1)).eventually
    (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hfast, eventually_ge_atTop (16896 : ℝ)] with L hfast hlarge
  have hL1 : 1 ≤ L := by linarith
  have hL : 0 < L := by linarith
  have hpow : 0 < L^a := Real.rpow_pos_of_pos hL a
  have he : Real.exp (-(L^c)) ≤ L^(-a) := by
    have hf : L^a*Real.exp (-(L^c)) ≤ 1 := by
      simpa only [neg_one_mul] using hfast.le
    calc
      _ ≤ 1/L^a := (le_div_iff₀ hpow).mpr (by nlinarith)
      _ = _ := by rw [Real.rpow_neg hL.le, one_div]
  have hH1 : 1 ≤ L^(d+3) := Real.one_le_rpow hL1 (by linarith)
  let T := L^(d+3)*L^(-a)
  have hbase : L^(-a) ≤ T := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hH1 (Real.rpow_nonneg hL.le (-a))
  intro U V r hU hV hr hUlarge hVlarge hrlo hrhi hlog
  have hrec (n : ℕ) (hn : Real.exp (L^c)/4 ≤ (n : ℝ)) : 1/(n : ℝ) ≤ 4*L^(-a) := by
    calc
      _ ≤ 1/(Real.exp (L^c)/4) :=
        one_div_le_one_div_of_le (by positivity) hn
      _ = 4*Real.exp (-(L^c)) := by rw [Real.exp_neg]; field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left he (by norm_num)
  have hq : 1/(L^a/2) = 2*L^(-a) := by rw [Real.rpow_neg hL.le]; field_simp
  have hu : L^(d+3)/(U : ℝ) ≤ 4*T := by
    calc
      _ = L^(d+3)*(1/(U : ℝ)) := by ring
      _ ≤ L^(d+3)*(4*L^(-a)) :=
        mul_le_mul_of_nonneg_left (hrec U hUlarge) (Real.rpow_nonneg hL.le _)
      _ = _ := by dsimp [T]; ring
  have hs : L^(d+3)/L^a = T := by dsimp only [T]; rw [Real.rpow_neg hL.le]; rfl
  have hsum : 1/(V : ℝ)+1/(L^a/2)+L^(d+3)/(U : ℝ)+L^(d+3)/L^a ≤ 11*T := by
    rw [hq, hs]
    have hv := (hrec V hVlarge).trans (mul_le_mul_of_nonneg_left hbase (by norm_num : (0 : ℝ) ≤ 4))
    have hqb := mul_le_mul_of_nonneg_left hbase (by norm_num : (0 : ℝ) ≤ 2)
    linarith
  have hg := (idealMinorGramBudget_branch U V r hU hV hr
    (Q := L^a/2) (S := L^a) (H := L^(d+3)) (by positivity) hpow hrlo hrhi hlog).trans
    (mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 24))
  calc
    _ ≤ 64*L^(2*κ)*(24*(11*T)) :=
      mul_le_mul_of_nonneg_left hg (by positivity)
    _ = 16896*L^(-2*E-9) := by
      dsimp only [T]
      rw [show 64*L^(2*κ)*(24*(11*(L^(d+3)*L^(-a)))) =
          16896*(L^(2*κ)*L^(d+3)*L^(-a)) by ring,
        ← Real.rpow_add hL, ← Real.rpow_add hL]
      congr 1
      dsimp [a, idealMinorCutoffExponent]
      ring
    _ ≤ L*L^(-2*E-9) :=
      mul_le_mul_of_nonneg_right hlarge (Real.rpow_nonneg hL.le _)
    _ = L^(-2*E-8) := by
      nth_rw 1 [← Real.rpow_one L]
      rw [← Real.rpow_add hL]
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)

end
end ArtinMatthews
