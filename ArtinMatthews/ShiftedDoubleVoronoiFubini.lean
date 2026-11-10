module

public import ArtinMatthews.DoubleVoronoiDualAverage
public import ArtinMatthews.ShiftedVoronoiResidue
public import ArtinMatthews.DoubleVoronoiCompleteAverage
public import ArtinMatthews.ShiftedDoubleVoronoi
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Monotonicity.Lemmas
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

/-! Absolute convergence and finite averaging for the actual transformed
coefficient pairs. Finite a,j averages are interchanged with the double Bessel
sum using proved summability, before applying the exact arithmetic identity. -/

noncomputable section
open Complex UpperHalfPlane Set Finset
open scoped MatrixGroups ContDiff
open OAI.Erdos970.ErdosKloosterman

namespace ArtinMatthews

/-- The untwisted coefficient product of the separable source test. -/
def cuspSourcePair {F : Type*} [FunLike F ℍ ℂ] (f : F)
    (H1 H2 : ℝ → ℂ) (k : ℕ × ℕ) : ℂ :=
  (qExpansion 1 f).coeff k.1 * (qExpansion 1 f).coeff k.2 * H1 k.1 * H2 k.2

/-- The untwisted coefficient product at the actual dual Bessel scale q². -/
def cuspBesselPair {F : Type*} [FunLike F ℍ ℂ] (f : F) (q : ℕ)
    (H1 H2 : ℝ → ℂ) (k : ℕ × ℕ) : ℂ :=
  cuspSourcePair f
    (fun x ↦ weightOneBesselTransform H1 (x / (q : ℝ)^2))
    (fun x ↦ weightOneBesselTransform H2 (x / (q : ℝ)^2)) k

/-- Absolute convergence of the untwisted source pair. -/
theorem cuspSourcePair_summable
    (N : ℕ) [NeZero N] (f : CuspForm (cubicThetaKernel N) 1)
    (H1 H2 : ℝ → ℂ) (hs1 : ContDiff ℝ ∞ H1) (hs2 : ContDiff ℝ ∞ H2)
    (u1 v1 u2 v2 : ℝ) (hu1 : 0 < u1) (hu2 : 0 < u2)
    (hw1 : Function.support H1 ⊆ Icc u1 v1) (hw2 : Function.support H2 ⊆ Icc u2 v2) :
    Summable (cuspSourcePair f H1 H2) := by
  have h1 := weightOne_source_residue_summable f (cubicThetaKernel_periodOne N) 1 0
    H1 hs1 u1 v1 hu1 hw1
  have h2 := weightOne_source_residue_summable f (cubicThetaKernel_periodOne N) 1 0
    H2 hs2 u2 v2 hu2 hw2
  simp only [cuspResidueCoeff, zero_mul, AddChar.map_zero_eq_one, mul_one] at h1 h2
  have h := summable_mul_of_summable_norm
    (f := fun n : ℕ ↦ (qExpansion 1 f).coeff n * H1 n)
    (g := fun n : ℕ ↦ (qExpansion 1 f).coeff n * H2 n) h1.norm h2.norm
  convert h using 1
  ext k
  unfold cuspSourcePair
  ring

/-- Absolute convergence of the untwisted dual pair. -/
theorem cuspBesselPair_summable
    (N : ℕ) [NeZero N] (f : CuspForm (cubicThetaKernel N) 1)
    (q : ℕ) [NeZero q]
    (H1 H2 : ℝ → ℂ) (hs1 : ContDiff ℝ ∞ H1) (hs2 : ContDiff ℝ ∞ H2)
    (u1 v1 u2 v2 : ℝ) (hu1 : 0 < u1) (hu2 : 0 < u2)
    (hw1 : Function.support H1 ⊆ Icc u1 v1) (hw2 : Function.support H2 ⊆ Icc u2 v2) :
    Summable (cuspBesselPair f q H1 H2) := by
  have h := weightOne_double_dual_summable N f q 0 0 H1 H2 hs1 hs2 u1 v1 u2 v2 hu1 hu2 hw1 hw2
  simp only [cuspResidueCoeff, zero_mul, AddChar.map_zero_eq_one, mul_one] at h
  convert h using 1
  ext k
  unfold cuspBesselPair cuspSourcePair
  ring

/-- A unit-modulus phase preserves absolute convergence. -/
theorem summable_mul_stdAddChar {ι : Type*} (q : ℕ) [NeZero q]
    (A : ι → ℂ) (hA : Summable A) (P : ι → ZMod q) :
    Summable (fun k ↦ A k * ZMod.stdAddChar (P k)) := by
  apply hA.norm.of_norm_bounded
  intro k
  simp only [norm_mul, AddChar.norm_apply, mul_one, le_refl]

/-- Exact finite Fubini with a normalized outer average. Its summability input
is discharged by the actual source and Bessel pair theorems above. -/
theorem doubleVoronoi_finite_average_tsum {ι α β : Type*} [Fintype α] [Fintype β]
    (q d : ℕ) [NeZero q] (A : ι → ℂ) (hA : Summable A) (P : α → β → ι → ZMod q) :
    (∑ a : α, ∑ j : β, ∑' k : ι, A k * ZMod.stdAddChar (P a j k)) / (d : ℂ) =
      ∑' k : ι, A k * ((∑ a : α, ∑ j : β, ZMod.stdAddChar (P a j k)) / (d : ℂ)) := by
  have hs (a : α) (j : β) := summable_mul_stdAddChar q A hA (P a j)
  have hj (a : α) : Summable (fun k ↦ ∑ j : β, A k * ZMod.stdAddChar (P a j k)) :=
    summable_sum (fun j _ ↦ hs a j)
  simp_rw [← Summable.tsum_finsetSum (s := univ) (fun j _ ↦ hs _ j)]
  rw [← Summable.tsum_finsetSum (s := univ) (fun a _ ↦ hj a)]
  rw [← tsum_div_const]
  apply tsum_congr
  intro k
  simp_rw [← Finset.mul_sum]
  ring

/-- The arithmetic complete-average identity applied to the actual convergent
Bessel coefficient sequence. This is the dual analytic content of (5.9). -/
theorem weightOne_dual_average_kloosterman
    (N : ℕ) [NeZero N] (f : CuspForm (cubicThetaKernel N) 1)
    (H d r : ℕ) [NeZero H] [NeZero d]
    (hdH : d∣H) (hQ : (d*r)^2∣H*d) (hr : r≠0)
    (m3 m4 A0 : ℤ) (hfactor : m3-m4=(r : ℤ)*A0) (hcop : IsCoprime (d : ℤ) (m3*A0))
    (v3 v4 : (ZMod (H*d))ˣ)
    (hv3 : (v3 : ZMod (H*d))=(m3 : ZMod (H*d)))
    (hv4 : (v4 : ZMod (H*d))=(m4 : ZMod (H*d)))
    (H1 H2 : ℝ → ℂ) (hs1 : ContDiff ℝ ∞ H1) (hs2 : ContDiff ℝ ∞ H2)
    (u1 v1 u2 v2 : ℝ) (hu1 : 0 < u1) (hu2 : 0 < u2)
    (hw1 : Function.support H1 ⊆ Icc u1 v1) (hw2 : Function.support H2 ⊆ Icc u2 v2) :
    (∑ a : (ZMod (H*d))ˣ, ∑ j : ZMod d, ∑' k : ℕ × ℕ,
      cuspBesselPair f (H*d) H1 H2 k *
        ZMod.stdAddChar (doubleVoronoiDualPhase H d hdH v3 v4 a k.1 k.2 j)) / (d : ℂ) =
      ∑' k : ℕ × ℕ, cuspBesselPair f (H*d) H1 H2 k *
        ((if Int.ModEq ((d : ℤ)*(r : ℤ)) (m3^2*k.1) (m4^2*k.2) then 1 else 0) *
          sum ZMod.stdAddChar ((v3 : ZMod (H*d))-(v4 : ZMod (H*d)))
            ((↑(v3*v4)⁻¹ : ZMod (H*d))*((v4 : ZMod (H*d))*k.2-(v3 : ZMod (H*d))*k.1))) := by
  rw [doubleVoronoi_finite_average_tsum (H*d) d _
    (cuspBesselPair_summable N f (H*d) H1 H2 hs1 hs2 u1 v1 u2 v2 hu1 hu2 hw1 hw2)]
  apply tsum_congr
  intro k
  congr 1
  simpa only [Int.cast_natCast] using doubleVoronoi_complete_average H d r hdH hQ hr
    m3 m4 k.1 k.2 A0 hfactor hcop v3 v4 hv3 hv4

end ArtinMatthews
