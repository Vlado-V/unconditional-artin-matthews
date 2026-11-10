module

public import ArtinMatthews.PrincipalDedekindReciprocal
public import ArtinMatthews.PrincipalAngularCorrection
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! Uniform angular nonvanishing and the actual finite-S Dedekind residue.
The global Poisson integral is not identified with these factors here. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField Set Filter
open scoped NumberField Classical Topology
noncomputable section
variable {K : Type*} [Field K] [NumberField K] {ζ : K} {M : Ideal (𝓞 K)}

theorem principalAngularCorrection_inv_norm_le (hζ : IsPrimitiveRoot ζ 12)
    (η : EvenIdealRayCharacter K M) (S : Finset (ArtinMatthews.ProbePrime K))
    (hS : principalAngularCutoff K M ⊆ S) {s : ℂ} (hs : 99799 / 100000 ≤ s.re) :
    ‖(principalAngularCorrection hζ η S s)⁻¹‖ ≤ probeGoodProductUniformBound K := by
  have hcut := probePrimeCutoff_subset_principalAngularCutoff.trans hS
  have hp := principalAngular_point_region hs
  rw [principalAngularCorrection, ArtinMatthews.probeEulerProduct_eq_exp K S hcut _ _ _
    (by simp) (fun P => η.allCoefficient_norm_le_one P.asIdeal)
    (fun P => principalAngularThirdPhase_norm_le_one hζ η P) hp, ← Complex.exp_neg]
  apply (Complex.norm_exp_le_exp_norm _).trans
  apply Real.exp_le_exp.mpr
  rw [norm_neg]
  exact (ArtinMatthews.probeEulerLog_norm_le K S hcut _ _ _ (by simp)
    (fun P => η.allCoefficient_norm_le_one P.asIdeal)
    (fun P => principalAngularThirdPhase_norm_le_one hζ η P) hp).trans
    (probeEulerLogMajorant_le_all K S)

theorem principalAngularCorrection_norm_lower (hζ : IsPrimitiveRoot ζ 12)
    (η : EvenIdealRayCharacter K M) (S : Finset (ArtinMatthews.ProbePrime K))
    (hS : principalAngularCutoff K M ⊆ S) {s : ℂ} (hs : 99799 / 100000 ≤ s.re) :
    (probeGoodProductUniformBound K)⁻¹ ≤ ‖principalAngularCorrection hζ η S s‖ := by
  have hn := principalAngularCorrection_ne_zero hζ η S hS hs
  have hi := principalAngularCorrection_inv_norm_le hζ η S hS hs
  have he : ‖principalAngularCorrection hζ η S s‖ *
      ‖(principalAngularCorrection hζ η S s)⁻¹‖ = 1 := by
    rw [← norm_mul, mul_inv_cancel₀ hn, norm_one]
  rw [inv_eq_one_div]
  apply (div_le_iff₀ (probeGoodProductUniformBound_pos K)).mpr
  have h := mul_le_mul_of_nonneg_left hi (norm_nonneg (principalAngularCorrection hζ η S s))
  nlinarith

theorem principalAngularCorrection_one_ne_zero (hζ : IsPrimitiveRoot ζ 12)
    (η : EvenIdealRayCharacter K M) (S : Finset (ArtinMatthews.ProbePrime K))
    (hS : principalAngularCutoff K M ⊆ S) : principalAngularCorrection hζ η S 1 ≠ 0 :=
  principalAngularCorrection_ne_zero hζ η S hS (by norm_num)

def principalZetaEulerFactor (S : Finset (ArtinMatthews.ProbePrime K)) (s : ℂ) : ℂ :=
  ∏ P ∈ S, (1 - (Ideal.absNorm P.asIdeal : ℂ) ^ (-s))

theorem principalZetaEulerFactor_entire (S : Finset (ArtinMatthews.ProbePrime K)) :
    Differentiable ℂ (principalZetaEulerFactor S) := by
  unfold principalZetaEulerFactor
  apply Differentiable.fun_finsetProd
  intro P _
  apply Differentiable.const_sub
  exact differentiable_id.neg.const_cpow (Or.inl (by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr P.ne_bot))

theorem principalZetaEulerFactor_one_ne_zero (S : Finset (ArtinMatthews.ProbePrime K)) :
    principalZetaEulerFactor S 1 ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro P _
  have hQ := probeIdealPrime_norm_gt_one K P
  have hn : ‖(Ideal.absNorm P.asIdeal : ℂ) ^ (-(1 : ℂ))‖ < 1 := by
    rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ (by norm_num)
  intro he
  rw [← sub_eq_zero.mp he, norm_one] at hn
  exact (lt_irrefl _ hn)

def principalExteriorZetaRegularized (S : Finset (ArtinMatthews.ProbePrime K)) (s : ℂ) : ℂ :=
  principalDedekindRegularized K s * principalZetaEulerFactor S s

def principalExteriorZeta (S : Finset (ArtinMatthews.ProbePrime K)) (s : ℂ) : ℂ :=
  mixedDedekindZeta K s * principalZetaEulerFactor S s

def principalExteriorZetaResidue (K : Type*) [Field K] [NumberField K]
    (S : Finset (ArtinMatthews.ProbePrime K)) : ℂ :=
  (dedekindZeta_residue K : ℂ) * principalZetaEulerFactor S 1

theorem principalExteriorZetaRegularized_entire (S : Finset (ArtinMatthews.ProbePrime K)) :
    Differentiable ℂ (principalExteriorZetaRegularized S) :=
  (principalDedekindRegularized_entire K).mul (principalZetaEulerFactor_entire S)

theorem principalExteriorZetaRegularized_one (S : Finset (ArtinMatthews.ProbePrime K)) :
    principalExteriorZetaRegularized S 1 = principalExteriorZetaResidue K S := by
  rw [principalExteriorZetaRegularized, principalDedekindRegularized_one]
  rfl

theorem principalExteriorZetaResidue_ne_zero (S : Finset (ArtinMatthews.ProbePrime K)) :
    principalExteriorZetaResidue K S ≠ 0 :=
  mul_ne_zero (Complex.ofReal_ne_zero.mpr (dedekindZeta_residue_ne_zero K))
    (principalZetaEulerFactor_one_ne_zero S)

theorem principalExteriorZetaRegularized_eq (S : Finset (ArtinMatthews.ProbePrime K))
    {s : ℂ} (hs : s ≠ 1) :
    principalExteriorZetaRegularized S s = (s - 1) * principalExteriorZeta S s := by
  rw [principalExteriorZetaRegularized, principalExteriorZeta, principalDedekindRegularized_eq_zeta K hs]
  ring

theorem principalExteriorZeta_residue_limit (S : Finset (ArtinMatthews.ProbePrime K)) :
    Tendsto (fun s : ℂ => (s - 1) * principalExteriorZeta S s)
      (𝓝[≠] 1) (𝓝 (principalExteriorZetaResidue K S)) := by
  have ht : Tendsto (principalExteriorZetaRegularized S) (𝓝[≠] 1)
      (𝓝 (principalExteriorZetaRegularized S 1)) :=
    ((principalExteriorZetaRegularized_entire S).continuous.continuousAt).tendsto.mono_left
      nhdsWithin_le_nhds
  rw [principalExteriorZetaRegularized_one] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact principalExteriorZetaRegularized_eq S hs

theorem principalExteriorZeta_scaled_residue_limit (S : Finset (ArtinMatthews.ProbePrime K)) :
    Tendsto (fun z : ℂ => (z - 1 / 6) * principalExteriorZeta S (6 * z))
      (𝓝[≠] (1 / 6 : ℂ)) (𝓝 (principalExteriorZetaResidue K S / 6)) := by
  have hd : Differentiable ℂ (fun z : ℂ => principalExteriorZetaRegularized S (6 * z) / 6) :=
    ((principalExteriorZetaRegularized_entire S).comp (differentiable_id.const_mul 6)).div_const 6
  have ht : Tendsto (fun z : ℂ => principalExteriorZetaRegularized S (6 * z) / 6)
      (𝓝[≠] (1 / 6 : ℂ)) (𝓝 (principalExteriorZetaRegularized S (6 * (1 / 6)) / 6)) :=
    hd.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  norm_num only [show (6 : ℂ) * (1 / 6) = 1 by norm_num,
    principalExteriorZetaRegularized_one] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz' : z ≠ (1 / 6 : ℂ) := by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hz
  have h6 : (6 : ℂ) * z ≠ 1 := by
    intro he
    apply hz'
    linear_combination (1 / 6 : ℂ) * he
  rw [principalExteriorZetaRegularized_eq S h6]
  ring

theorem principalAngular_doubleResidueCoefficient_ne_zero (hζ : IsPrimitiveRoot ζ 12)
    (η : EvenIdealRayCharacter K M) (S : Finset (ArtinMatthews.ProbePrime K))
    (hS : principalAngularCutoff K M ⊆ S) {s : ℂ} (hs : 99799 / 100000 ≤ s.re) :
    (principalExteriorZetaResidue K S ^ 2 / 6) * principalAngularCorrection hζ η S s ≠ 0 :=
  mul_ne_zero (div_ne_zero (pow_ne_zero _ (principalExteriorZetaResidue_ne_zero S)) (by norm_num))
    (principalAngularCorrection_ne_zero hζ η S hS hs)

end
end ArtinMatthews.VaryingKummerAnalytic
