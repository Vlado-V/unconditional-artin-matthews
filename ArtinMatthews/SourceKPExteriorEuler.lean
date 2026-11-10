module

public import ArtinMatthews.SourceKPExteriorScattering
public import ArtinMatthews.ProbeIdealSourceRegions
public import ArtinMatthews.SourceKPPrimeIdealEuler
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open NumberField IsDedekindDomain VaryingKummerAnalytic
open scoped NumberField BigOperators
noncomputable section

variable {K : Type*} [Field K] [NumberField K]

theorem sourceKPPrimeIdealEulerFactor_ne_zero (P : ProbePrime K) {s : ℂ} (hs : 1 < s.re) :
    (1 - (Ideal.absNorm P.asIdeal : ℂ) ^ (-s))⁻¹ ≠ 0 := by
  apply inv_ne_zero
  have hn : ‖(Ideal.absNorm P.asIdeal : ℂ) ^ (-s)‖ < 1 := by
    rw [← Complex.ofReal_natCast,
      Complex.norm_cpow_eq_rpow_re_of_pos (lt_trans zero_lt_one (probeIdealPrime_norm_gt_one K P)),
      Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg (probeIdealPrime_norm_gt_one K P) (by linarith)
  intro he
  rw [← sub_eq_zero.mp he, norm_one] at hn
  exact (lt_irrefl _ hn)

theorem sourceKPExteriorZeta_hasProd (S : Finset (ProbePrime K)) {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun P : {P : ProbePrime K // P ∉ S} =>
      (1 - (Ideal.absNorm P.val.asIdeal : ℂ) ^ (-s))⁻¹) (principalExteriorZeta S s) := by
  let f := fun P : ProbePrime K => (1 - (Ideal.absNorm P.asIdeal : ℂ) ^ (-s))⁻¹
  let g := (↑S : Set (ProbePrime K))ᶜ |>.mulIndicator f
  have h := (sourceKPPrimeIdealEuler_hasProd K hs).congr_cofinite₀
    (g := g) (s := S) (fun P _ => sourceKPPrimeIdealEulerFactor_ne_zero P hs)
    (by intro P hP; simp [g, f, hP])
  have hfinite : (∏ P ∈ S, g P) / (∏ P ∈ S, f P) = principalZetaEulerFactor S s := by
    have hg : (∏ P ∈ S, g P) = 1 := by
      apply Finset.prod_eq_one
      intro P hP
      simp [g, hP]
    rw [hg]
    simp [f, principalZetaEulerFactor, Finset.prod_inv_distrib]
  rw [hfinite, ← mixedDedekindZeta_eq K hs] at h
  exact hasProd_subtype_iff_mulIndicator.mpr h

/-- This is the product of the local exterior factors at precisely the
places outside the supplied finite set. -/
theorem sourceKPExteriorScattering_hasProd (S : Finset (ProbePrime K)) {s : ℂ}
    (hs : 1/6 < s.re) :
    HasProd (fun P : {P : ProbePrime K // P ∉ S} => sourceKPUnramifiedScatteringFactor P.val s)
      (sourceKPExteriorScattering S s) := by
  have h₁ : 1 < (6*s).re := by
    have he : (6*s).re = 6*s.re := by norm_num [Complex.mul_re]
    rw [he]
    linarith
  have h₂ : 1 < (6*s+1).re := by simp only [Complex.add_re, Complex.one_re]; linarith
  have h := (sourceKPExteriorZeta_hasProd S h₁).div₀ (sourceKPExteriorZeta_hasProd S h₂)
    (sourceKPExteriorZeta_ne_zero S h₂)
  apply h.congr_fun
  intro P
  change (1 - (Ideal.absNorm P.val.asIdeal : ℂ) ^ (-(6*s+1))) /
      (1 - (Ideal.absNorm P.val.asIdeal : ℂ) ^ (-(6*s))) =
    (1 - (Ideal.absNorm P.val.asIdeal : ℂ) ^ (-(6*s)))⁻¹ /
      (1 - (Ideal.absNorm P.val.asIdeal : ℂ) ^ (-(6*s+1)))⁻¹
  simp only [div_eq_mul_inv, inv_inv]
  exact mul_comm _ _

end
end ArtinMatthews
