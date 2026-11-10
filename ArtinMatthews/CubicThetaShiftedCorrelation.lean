module

public import ArtinMatthews.CubicThetaCircleReduction
public import ArtinMatthews.ShiftedSourceCutoff
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Int.Star
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

/-! The literal shifted theta correlation is the finite source in the circle
reduction. Compact support makes this an exact equality, without a tail error. -/

noncomputable section
open Complex UpperHalfPlane Set OAI
open scoped BigOperators
namespace ArtinMatthews

local instance : FunLike (ℍ → ℂ) ℍ ℂ := ⟨id, Function.injective_id⟩

def thetaShiftedCorrelation (χ : SevenEighths.HeckeFamily.Character)
    (m1 m2 : ℕ) (g : ℝ → ℂ) : ℂ :=
  ∑' n : ℕ, idealThetaCoeff χ (m1*n+1) * idealThetaCoeff χ (m2*n+1) * g n

theorem thetaShiftedCorrelation_summable (χ : SevenEighths.HeckeFamily.Character)
    (m1 m2 : ℕ) (T : ℝ) (g : ℝ → ℂ) (hg : Function.support g ⊆ Icc T (2*T)) :
    Summable (fun n : ℕ => idealThetaCoeff χ (m1*n+1) * idealThetaCoeff χ (m2*n+1) * g n) := by
  apply summable_of_hasFiniteSupport
  apply (Finset.range (⌈2*T⌉₊ + 1)).finite_toSet.subset
  intro n hn
  have hgn : g n ≠ 0 := by
    intro hz
    exact hn (by simp only [hz, mul_zero])
  have hb : (n : ℝ) ≤ ⌈2*T⌉₊ := (hg hgn).2.trans (Nat.le_ceil (2*T))
  have hnle : n ≤ ⌈2*T⌉₊ := by exact_mod_cast hb
  exact Finset.mem_range.mpr (by omega)

theorem thetaShiftedSourcePair_eq (χ : SevenEighths.HeckeFamily.Character)
    (m1 m2 : ℕ) (hm1 : 0 < m1) (hm2 : 0 < m2) (T : ℝ) (hT : 0 < T)
    (g : ℝ → ℂ) (hg : Function.support g ⊆ Icc T (2*T)) (n : ℕ) :
    cuspSourcePair (heckeTheta χ) (shiftedSourceTest g m1) (shiftedSourceMajorant m2 T)
      (m1*n+1, m2*n+1) =
      idealThetaCoeff χ (m1*n+1) * idealThetaCoeff χ (m2*n+1) * g n := by
  unfold cuspSourcePair
  change (qExpansion 1 (heckeTheta χ)).coeff (m1*n+1) *
    (qExpansion 1 (heckeTheta χ)).coeff (m2*n+1) *
    shiftedSourceTest g m1 (m1*n+1 : ℕ) * shiftedSourceMajorant m2 T (m2*n+1 : ℕ) = _
  rw [heckeTheta_qExpansion_coeff, heckeTheta_qExpansion_coeff]
  push_cast
  rw [mul_assoc (idealThetaCoeff χ (m1*n+1) * idealThetaCoeff χ (m2*n+1))]
  congr 1
  exact shiftedSourceTest_product g T m1 m2 n hT
    (by exact_mod_cast hm1) (by exact_mod_cast hm2) hg

theorem thetaShiftedCorrelation_eq_finite (χ : SevenEighths.HeckeFamily.Character)
    (m1 m2 T1 T2 : ℕ) (hm1 : 0 < m1) (hm2 : 0 < m2) (T : ℝ) (hT : 0 < T)
    (g : ℝ → ℂ) (hg : Function.support g ⊆ Icc T (2*T))
    (hT1 : 1 + 2*(m1 : ℝ)*T ≤ T1) (hT2 : 1 + 2*(m2 : ℝ)*T ≤ T2) :
    thetaShiftedCorrelation χ m1 m2 g =
      thetaShiftedFiniteSum χ m1 m2 T1 T2 (shiftedSourceTest g m1) (shiftedSourceMajorant m2 T) := by
  unfold thetaShiftedCorrelation thetaShiftedFiniteSum
  rw [tsum_eq_sum (s := (Finset.range (T1+1)).filter (fun n => m1*n+1 ≤ T1 ∧ m2*n+1 ≤ T2)) ?_]
  · apply Finset.sum_congr rfl
    intro n _
    exact (thetaShiftedSourcePair_eq χ m1 m2 hm1 hm2 T hT g hg n).symm
  · intro n hn
    have hz : g n = 0 := by
      by_contra hnz
      have hgn := hg hnz
      have h1 : m1*n+1 ≤ T1 := by
        have hi : (m1 : ℝ)*n+1 ≤ T1 := by
          nlinarith [mul_le_mul_of_nonneg_left hgn.2 (Nat.cast_nonneg m1)]
        exact_mod_cast hi
      have h2 : m2*n+1 ≤ T2 := by
        have hi : (m2 : ℝ)*n+1 ≤ T2 := by
          nlinarith [mul_le_mul_of_nonneg_left hgn.2 (Nat.cast_nonneg m2)]
        exact_mod_cast hi
      have hn1 : n ≤ m1*n := by nlinarith
      exact hn (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), h1, h2⟩)
    simp only [hz, mul_zero]

end ArtinMatthews
