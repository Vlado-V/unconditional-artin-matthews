module

public import ArtinMatthews.PrincipalAngularResidue
public import ArtinMatthews.ProbeIdealSourceRegions
public import ArtinMatthews.VaryingKummerAnalyticDedekindNonvanishing
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

/-! The meromorphic exterior factor of the normalized cubic spherical
intertwiner. The parameter is the exponent on the ratio of the two
diagonal entries, before the modular half factor. At the exceptional
parameter `1/6`, the class-number residue is multiplied by `1/6`
from the change of variable `s ↦ 6*s`. -/

namespace ArtinMatthews
open NumberField VaryingKummerAnalytic Filter
open scoped NumberField Topology BigOperators
noncomputable section

variable {K : Type*} [Field K] [NumberField K]

def sourceKPUnramifiedScatteringFactor (P : ProbePrime K) (s : ℂ) : ℂ :=
  (1 - (Ideal.absNorm P.asIdeal : ℂ) ^ (-(6*s + 1))) /
    (1 - (Ideal.absNorm P.asIdeal : ℂ) ^ (-(6*s)))

/-- The deleted primes are precisely those at which a separate local
operator is required. This factor accounts for no operator at those primes. -/
def sourceKPExteriorScattering (S : Finset (ProbePrime K)) (s : ℂ) : ℂ :=
  principalExteriorZeta S (6*s) / principalExteriorZeta S (6*s + 1)

def sourceKPExteriorScatteringRegularized (S : Finset (ProbePrime K)) (s : ℂ) : ℂ :=
  principalExteriorZetaRegularized S (6*s) / (6 * principalExteriorZeta S (6*s + 1))

def sourceKPExteriorScatteringResidue (S : Finset (ProbePrime K)) : ℂ :=
  principalExteriorZetaResidue K S / (6 * principalExteriorZeta S 2)

theorem sourceKPExteriorZeta_analyticAt (S : Finset (ProbePrime K)) {s : ℂ} (hs : s ≠ 1) :
    AnalyticAt ℂ (principalExteriorZeta S) s :=
  (mixedDedekindZeta_analyticAt K hs).mul ((principalZetaEulerFactor_entire S).analyticAt s)

theorem sourceKPExteriorZeta_ne_zero (S : Finset (ProbePrime K)) {s : ℂ} (hs : 1 < s.re) :
    principalExteriorZeta S s ≠ 0 := by
  rw [principalExteriorZeta, mixedDedekindZeta_eq K hs]
  refine mul_ne_zero (dedekindZeta_ne_zero_of_one_lt_re K hs) (Finset.prod_ne_zero_iff.mpr ?_)
  intro P _
  have hQ := probeIdealPrime_norm_gt_one K P
  have h : ‖(Ideal.absNorm P.asIdeal : ℂ) ^ (-s)‖ < 1 := by
    rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith), Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ (by linarith)
  intro he
  rw [← sub_eq_zero.mp he, norm_one] at h
  exact (lt_irrefl _ h)

theorem sourceKPExteriorZeta_meromorphic (S : Finset (ProbePrime K)) :
    Meromorphic (principalExteriorZeta S) := by
  intro z
  exact (mixedDedekindZeta_meromorphic K z).mul
    (((principalZetaEulerFactor_entire S).analyticAt z).meromorphicAt)

theorem sourceKPExteriorScattering_meromorphic (S : Finset (ProbePrime K)) :
    Meromorphic (sourceKPExteriorScattering S) := by
  intro s
  have h₁ : AnalyticAt ℂ (fun z : ℂ => 6*z) s := analyticAt_const.mul analyticAt_id
  have h₂ : AnalyticAt ℂ (fun z : ℂ => 6*z+1) s := h₁.add analyticAt_const
  have hn := (sourceKPExteriorZeta_meromorphic S (6*s)).comp_analyticAt
    (g := fun z : ℂ => 6*z) h₁
  have hd := (sourceKPExteriorZeta_meromorphic S (6*s+1)).comp_analyticAt
    (g := fun z : ℂ => 6*z+1) h₂
  exact hn.div hd

theorem sourceKPExteriorScatteringRegularized_analyticAt (S : Finset (ProbePrime K)) :
    AnalyticAt ℂ (sourceKPExteriorScatteringRegularized S) (1 / 6) := by
  have h₁ : AnalyticAt ℂ (fun z : ℂ => 6*z) (1/6) := analyticAt_const.mul analyticAt_id
  have h₂ : AnalyticAt ℂ (fun z : ℂ => 6*z+1) (1/6) := h₁.add analyticAt_const
  have htwo : 6 * (1 / 6 : ℂ) + 1 = 2 := by norm_num
  have hζ := sourceKPExteriorZeta_analyticAt S (s := 6 * (1 / 6 : ℂ) + 1)
    (by rw [htwo]; norm_num)
  exact (((principalExteriorZetaRegularized_entire S).analyticAt _).comp h₁).div
    (analyticAt_const.mul (hζ.comp (f := fun z : ℂ => 6*z+1) h₂))
    (mul_ne_zero (by norm_num) (by rw [htwo]; exact sourceKPExteriorZeta_ne_zero S (by norm_num)))

theorem sourceKPExteriorScatteringRegularized_value (S : Finset (ProbePrime K)) :
    sourceKPExteriorScatteringRegularized S (1 / 6) = sourceKPExteriorScatteringResidue S := by
  unfold sourceKPExteriorScatteringRegularized sourceKPExteriorScatteringResidue
  rw [show 6 * (1 / 6 : ℂ) = 1 by norm_num, principalExteriorZetaRegularized_one,
    show (1 : ℂ) + 1 = 2 by norm_num]

theorem sourceKPExteriorScatteringResidue_ne_zero (S : Finset (ProbePrime K)) :
    sourceKPExteriorScatteringResidue S ≠ 0 :=
  div_ne_zero (principalExteriorZetaResidue_ne_zero S)
    (mul_ne_zero (by norm_num) (sourceKPExteriorZeta_ne_zero S (by norm_num)))

theorem sourceKPExteriorScatteringRegularized_eq (S : Finset (ProbePrime K)) {s : ℂ}
    (hs : s ≠ 1/6) :
    sourceKPExteriorScatteringRegularized S s = (s-1/6) * sourceKPExteriorScattering S s := by
  have h6 : 6 * s ≠ 1 := by
    intro h
    apply hs
    linear_combination (1 / 6 : ℂ) * h
  rw [sourceKPExteriorScatteringRegularized, sourceKPExteriorScattering,
    principalExteriorZetaRegularized_eq S h6]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The meromorphic order belongs to the exterior spherical factor. -/
theorem sourceKPExteriorScattering_order (S : Finset (ProbePrime K)) :
    meromorphicOrderAt (sourceKPExteriorScattering S) (1 / 6) = -1 := by
  let N := sourceKPExteriorScatteringRegularized S
  let D := fun s : ℂ => s - 1/6
  have hEq : sourceKPExteriorScattering S =ᶠ[𝓝[≠] (1 / 6 : ℂ)] N / D := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hne : s ≠ (1 / 6 : ℂ) := by simpa using hs
    exact (eq_div_iff (sub_ne_zero.mpr hne)).mpr (by
      change sourceKPExteriorScattering S s * (s-1/6) = sourceKPExteriorScatteringRegularized S s
      rw [sourceKPExteriorScatteringRegularized_eq S hne, mul_comm])
  have hN := sourceKPExteriorScatteringRegularized_analyticAt S
  have hNz : N (1/6) ≠ 0 := by
    rw [show N = sourceKPExteriorScatteringRegularized S from rfl,
      sourceKPExteriorScatteringRegularized_value]
    exact sourceKPExteriorScatteringResidue_ne_zero S
  have hNo : meromorphicOrderAt N (1 / 6) = 0 := by
    rw [hN.meromorphicOrderAt_eq, hN.analyticOrderAt_eq_zero.mpr hNz]
    rfl
  have hD : MeromorphicAt D (1/6) := (analyticAt_id.sub analyticAt_const).meromorphicAt
  rw [meromorphicOrderAt_congr hEq, meromorphicOrderAt_div hN.meromorphicAt hD, hNo,
    meromorphicOrderAt_id_sub_const]
  norm_num

theorem sourceKPExteriorScattering_residue (S : Finset (ProbePrime K)) :
    Tendsto (fun s : ℂ => (s-1/6) * sourceKPExteriorScattering S s)
      (𝓝[≠] (1 / 6 : ℂ)) (𝓝 (sourceKPExteriorScatteringResidue S)) := by
  have h := (sourceKPExteriorScatteringRegularized_analyticAt S).continuousAt.tendsto.mono_left
    (show 𝓝[≠] (1 / 6 : ℂ) ≤ 𝓝 (1 / 6 : ℂ) from nhdsWithin_le_nhds)
  rw [sourceKPExteriorScatteringRegularized_value] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact sourceKPExteriorScatteringRegularized_eq S (by simpa using hs)

end
end ArtinMatthews
