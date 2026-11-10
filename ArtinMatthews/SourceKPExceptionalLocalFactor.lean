module

public import ArtinMatthews.SourceKPExteriorScattering
public import ArtinMatthews.ProbeIdealSourceRegions
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! At the exceptional parameter the unramified intertwining factor is
the factor in the finite-S normalization from the KP erratum. -/

namespace ArtinMatthews
open NumberField VaryingKummerAnalytic
open scoped NumberField BigOperators
noncomputable section

variable {K : Type*} [Field K] [NumberField K]

theorem sourceKPUnramifiedScatteringFactor_exceptional (P : ProbePrime K) :
    sourceKPUnramifiedScatteringFactor P (1/6) = 1 + (Ideal.absNorm P.asIdeal : ℂ)⁻¹ := by
  let Q : ℂ := Ideal.absNorm P.asIdeal
  have hQ : (1 : ℝ) < Ideal.absNorm P.asIdeal := probeIdealPrime_norm_gt_one K P
  have hQ0 : Q ≠ 0 := by
    dsimp only [Q]
    exact_mod_cast ne_of_gt (lt_trans zero_lt_one hQ)
  have hQ1 : 1 - Q⁻¹ ≠ 0 := by
    intro h
    have h' : Q = 1 := inv_eq_one.mp ((sub_eq_zero.mp h).symm)
    have hre := congrArg Complex.re h'
    dsimp only [Q] at hre
    norm_cast at hre
    norm_num [hre] at hQ
  have h2 : Q ^ (-(2 : ℂ)) = (Q^2)⁻¹ := by
    rw [Complex.cpow_neg]
    norm_cast
  unfold sourceKPUnramifiedScatteringFactor
  norm_num only [show (6 : ℂ) * (1/6) = 1 by norm_num, show (1 : ℂ)+1=2 by norm_num]
  change (1-Q^(-(2 : ℂ)))/(1-Q^(-(1 : ℂ))) = 1+Q⁻¹
  rw [h2, Complex.cpow_neg_one]
  have hf : 1-(Q^2)⁻¹ = (1+Q⁻¹)*(1-Q⁻¹) := by
    field_simp
    ring
  rw [hf, mul_div_cancel_right₀ _ hQ1]

theorem sourceKPUnramifiedScatteringFactor_exceptional_ne_zero (P : ProbePrime K) :
    sourceKPUnramifiedScatteringFactor P (1/6) ≠ 0 := by
  rw [sourceKPUnramifiedScatteringFactor_exceptional]
  have h : 0 < 1 + (Ideal.absNorm P.asIdeal : ℝ)⁻¹ := by positivity
  have hc := Complex.ofReal_ne_zero.mpr (ne_of_gt h)
  simpa only [Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_inv, Complex.ofReal_natCast] using hc

theorem sourceKPExceptionalFiniteNormalization (S : Finset (ProbePrime K)) :
    (∏ P ∈ S, sourceKPUnramifiedScatteringFactor P (1/6)) =
      ∏ P ∈ S, (1 + (Ideal.absNorm P.asIdeal : ℂ)⁻¹) := by
  apply Finset.prod_congr rfl
  intro P _
  exact sourceKPUnramifiedScatteringFactor_exceptional P

end
end ArtinMatthews
