module

public import ArtinMatthews.PrincipalDedekindAbsoluteContour
public import ArtinMatthews.SourceContinuedPoissonRowKernel
public import ArtinMatthews.SourcePoissonGoodHeightMajorants
public import ArtinMatthews.SourceProbeComparison
public import ArtinMatthews.SourceRowTwistDyadicExcluded
public import ArtinMatthews.SourceContinuedPoissonRowIntegral
public import ArtinMatthews.SourcePoissonLowKernelDecay
public import ArtinMatthews.SourceRowEulerContourDomain
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

/-! The pointwise good-row inputs use the true finite-box reciprocal
and the exact continued kernel. The same power bound applies to the
right tail using absolute Euler convergence. -/
namespace ArtinMatthews.SourcePhysical
open VaryingKummerAnalytic
noncomputable section

theorem sourcePoissonHeight_central_pointwise (n : ℕ) (y t x : ℝ) :
    sourceContourHeightWeight y*(Real.exp (-((x+t)^2))/(1+|t|)^(n+2)) ≤
      sourcePoissonHeightMoment 0 ((y,t),x) := by
  have hP : (1+|t|)^2 ≤ (1+|t|)^(n+2) :=
    pow_le_pow_right₀ (by linarith [abs_nonneg t]) (by omega)
  have hp : ((1+|t|)^(n+2))⁻¹ ≤ ((1+|t|)^2)⁻¹ := by
    rw [← one_div, ← one_div]
    exact one_div_le_one_div_of_le (by positivity) hP
  rw [div_eq_mul_inv, sourcePoissonHeightMoment, sourcePoissonHeightPolynomial]
  simp only [pow_zero, one_mul]
  have h := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hp.trans (sourcePoissonHeightWeight_of_one_add_abs_sq t))
      (sourceContourHeightWeight_nonneg y)) (Real.exp_nonneg (-((x+t)^2)))
  exact (by simpa only [mul_assoc, mul_left_comm, mul_comm] using h)

theorem sourcePoissonLowExponent_le {a : ℝ} (ha : a ≤ principalProbeSigma) :
    sourceContourExponent a (3/1000) (2/5) ≤ sourceContourExponent principalProbeSigma (3/1000) (2/5) := by
  unfold sourceContourExponent
  linarith

theorem sourcePoissonLowGaussian_le {a : ℝ} (ha : 499/500 ≤ a) (ha' : a ≤ principalProbeSigma) :
    Real.exp ((a+(2/5 : ℝ)-1)^2) ≤ Real.exp ((principalProbeSigma+(2/5 : ℝ)-1)^2) := by
  apply Real.exp_le_exp.mpr
  exact pow_le_pow_left₀ (by linarith) (by linarith) 2

end
end ArtinMatthews.SourcePhysical

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators Set
open VaryingKummerAnalytic SourcePhysical
open scoped NumberField Classical BigOperators
noncomputable section
variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable {J : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F J) (hJ : J ≠ ⊥)
local notation "S" => sourceHilbertSet F S₀
local notation "R" => sourceRing F S₀
local notation "K" => sourceContinuedPoissonRowKernel F S₀ hζ η hJ
local notation "Cw" => (3/1000 : ℝ)
local notation "Cz" => (2/5 : ℝ)

theorem sourceContinuedPoissonLowKernel_good_continuousOn
    (hcut : principalAngularCutoff F J ⊆ S) (v : InfinitePlace F)
    {ι : Type} [Fintype ι] (f : ι → {u : R // u ≠ 0}) (i : ι)
    (hu : ¬ ∃ x : F, x^6 = ((f i).val : F))
    (U r : ℝ) (hU : 0 ≤ U) (hr : 0 ≤ r) (hi : i ∉ sourceRowTwistDyadicExcludedRows F S₀ hζ η hJ f U r)
    {X Y Z : ℝ} (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (D : Set SourcePoissonHeights) (a x : SourcePoissonHeights → ℝ) (ha : Continuous a) (hx : Continuous x)
    (hre : ∀ p ∈ D, (499/500 : ℝ) ≤ a p) (him : ∀ p ∈ D, |x p| ≤ 4*U^r) :
    ContinuousOn (fun p => K v (f i) X Y Z (sourcePoissonVertical (a p) (x p),
      sourcePoissonVertical Cw p.1.1,sourcePoissonVertical Cz p.1.2)) D := by
  let q : SourcePoissonHeights → ProbeCoordinates := fun p =>
    (sourcePoissonVertical (a p) (x p),sourcePoissonVertical Cw p.1.1,sourcePoissonVertical Cz p.1.2)
  have hq : Continuous q := by unfold q sourcePoissonVertical; fun_prop
  apply (sourceContinuedPoissonRowKernel_continuousOn F S₀ hζ η hJ v (f i) hcut hu hX hY hZ).comp hq.continuousOn
  intro p hp
  exact ⟨sourceRowEulerOpenDomain_low_w_good F S₀ hζ η hJ f U r hU hr i hi (q p)
    (by simpa only [q,sourcePoissonVertical_re] using hre p hp)
    (by simp only [q,sourcePoissonVertical_re,le_rfl]) (by simp only [q,sourcePoissonVertical_re,le_rfl])
    (by simpa only [q,sourcePoissonVertical_im] using him p hp),
    by change 0 < (sourcePoissonVertical Cz p.1.2).re; rw [sourcePoissonVertical_re]; norm_num⟩

theorem exists_sourceContinuedPoissonLowKernel_decay_with_reciprocal_bound
    (hcut : principalAngularCutoff F J ⊆ S) (v : InfinitePlace F) (ε : ℝ) (hε : 0 < ε) (n : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ (u : {a : R // a ≠ 0}), (¬ ∃ x : F, x^6 = (u.val : F)) →
      ∀ U : ℝ, 0 < U → U ≤ sourcePoissonFrequencyNorm F S₀ u → sourcePoissonFrequencyNorm F S₀ u ≤ 2*U →
      ∀ Z : ℝ, 0 < Z → ∀ a : ℝ, (499/500 : ℝ) ≤ a → ∀ y t x B : ℝ,
      ‖sourceRowTwistReciprocal F hζ S₀ u.val u.property η hJ (sourcePoissonVertical a x)‖ ≤ B*U^(ε/2) →
      ‖K v u (Z^(9/10 : ℝ)) (Z^(133/1000 : ℝ)) Z
          (sourcePoissonVertical a x,sourcePoissonVertical Cw y,sourcePoissonVertical Cz t)‖ ≤
        (D*B*Z^(sourceContourExponent a Cw Cz)*Real.exp ((a+Cz-1)^2)*U^(1/10+ε))*
          (sourceContourHeightWeight y*(Real.exp (-((x+t)^2))/(1+|t|)^(n+2))) := by
  obtain ⟨D,hD,h⟩ := exists_sourceContinuedPoissonLowKernel_decay F S₀ hζ η hJ hcut v (ε/2) (by positivity) n
  refine ⟨D,hD,?_⟩
  intro u hu U hU hlo hhi Z hZ a ha y t x B hB
  apply (h u hu U hU hlo hhi Z hZ a ha y t x).trans
  apply mul_le_mul_of_nonneg_right _ (by
    exact mul_nonneg (sourceContourHeightWeight_nonneg _) (by positivity))
  have h := mul_le_mul_of_nonneg_left hB (show 0 ≤
      D*Z^(sourceContourExponent a Cw Cz)*Real.exp ((a+Cz-1)^2)*U^(1/10+ε/2) by positivity)
  refine h.trans_eq ?_
  calc
    _ = D*B*Z^(sourceContourExponent a Cw Cz)*Real.exp ((a+Cz-1)^2)*(U^(1/10+ε/2)*U^(ε/2)) := by ring
    _ = _ := by rw [← Real.rpow_add hU, show (1/10 : ℝ)+ε/2+ε/2 = 1/10+ε by ring]

end
end ArtinMatthews.SourceEulerAssembly
