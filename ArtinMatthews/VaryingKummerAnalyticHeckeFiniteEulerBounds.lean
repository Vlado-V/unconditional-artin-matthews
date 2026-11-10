module

public import ArtinMatthews.VaryingKummerAnalyticHeckeIdealMobius
public import ArtinMatthews.VaryingKummerAnalyticRayIdealMultiplicativity
public import ArtinMatthews.VaryingKummerAnalyticHeckeMobiusBound
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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

/-! Uniform subpower bounds for the actual finite Euler factors removed
at an ideal modulus. The loss is in its ideal norm; no rational enlargement
and no supplied bound on the number of its prime factors is used. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Complex
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section

theorem ideal_prime_support_norm_ge_two (K : Type*) [Field K] [NumberField K]
    {M P : Ideal (𝓞 K)} (hP : P ∈ HeckeIdealMobius.primeSupport K M) :
    2 ≤ Ideal.absNorm P := by
  have hp := HeckeIdealMobius.support_prime K hP
  have h0 : Ideal.absNorm P ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr hp.ne_zero
  have h1 : Ideal.absNorm P ≠ 1 := by
    intro h
    exact hp.not_isUnit (Ideal.isUnit_iff.mpr (Ideal.absNorm_eq_one_iff.mp h))
  omega

theorem norm_euler_ratio_le_three_quarters {N : ℝ} (hN : 2 ≤ N) {s : ℂ}
    (hs : (1/2 : ℝ) ≤ s.re) {a : ℂ} (ha : ‖a‖ ≤ 1) :
    ‖a*(N : ℂ)^(-s)‖ ≤ 3/4 := by
  have hN0 : 0 < N := by linarith
  have hx : 0 ≤ N^(-s.re) := Real.rpow_nonneg hN0.le _
  have hsq : (N^(-s.re))^2 ≤ (1/2 : ℝ) := by
    rw [← Real.rpow_mul_natCast hN0.le]
    calc
      _ ≤ N^(-(1 : ℝ)) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num; linarith)
      _ = 1/N := by rw [Real.rpow_neg_one,one_div]
      _ ≤ _ := one_div_le_one_div_of_le (by norm_num) hN
  have hpow : N^(-s.re) ≤ (3/4 : ℝ) := by nlinarith
  rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hN0,Complex.neg_re]
  exact (mul_le_of_le_one_left hx ha).trans hpow

theorem norm_one_sub_euler_ratio_bounds {N : ℝ} (hN : 2 ≤ N) {s : ℂ}
    (hs : (1/2 : ℝ) ≤ s.re) {a : ℂ} (ha : ‖a‖ ≤ 1) :
    ‖1-a*(N : ℂ)^(-s)‖ ≤ 2 ∧ ‖(1-a*(N : ℂ)^(-s))⁻¹‖ ≤ 4 := by
  have h := norm_euler_ratio_le_three_quarters hN hs ha
  have hl : (1/4 : ℝ) ≤ ‖1-a*(N : ℂ)^(-s)‖ := by
    have H := norm_sub_norm_le (1 : ℂ) (a*(N : ℂ)^(-s))
    rw [norm_one] at H
    linarith
  constructor
  · have H := norm_sub_le (1 : ℂ) (a*(N : ℂ)^(-s))
    rw [norm_one] at H
    linarith
  · rw [norm_inv]
    have H := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1/4) hl
    simpa only [one_div,inv_div,inv_one,mul_one,inv_inv] using H

namespace EvenIdealRayCharacter
variable {K : Type*} [Field K] [NumberField K] {f : Ideal (𝓞 K)}
variable (ψ : EvenIdealRayCharacter K f)

def idealEulerDeletion (M : Ideal (𝓞 K)) (s : ℂ) : ℂ :=
  ∏ P ∈ HeckeIdealMobius.primeSupport K M,
    (1-ψ.allCoefficient P*(Ideal.absNorm P : ℂ)^(-s))

theorem idealEulerDeletion_entire (M : Ideal (𝓞 K)) :
    Differentiable ℂ (ψ.idealEulerDeletion M) := by
  unfold idealEulerDeletion
  apply Differentiable.fun_finsetProd
  intro P hP
  apply Differentiable.const_sub
  apply Differentiable.const_mul
  exact differentiable_id.neg.const_cpow (Or.inl (by
    exact_mod_cast (show Ideal.absNorm P ≠ 0 by
      have H := ideal_prime_support_norm_ge_two K hP
      omega)))

theorem idealEulerDeletion_ne_zero (M : Ideal (𝓞 K)) {s : ℂ} (hs : 0 < s.re) :
    ψ.idealEulerDeletion M s ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro P hP
  have hN : 1 < (Ideal.absNorm P : ℝ) := by
    have H := ideal_prime_support_norm_ge_two K hP
    exact_mod_cast (show 1 < Ideal.absNorm P by omega)
  have H : ‖ψ.allCoefficient P*(Ideal.absNorm P : ℂ)^(-s)‖ < 1 := by
    rw [norm_mul,← Complex.ofReal_natCast,Complex.norm_cpow_eq_rpow_re_of_pos (by linarith),Complex.neg_re]
    exact (mul_le_of_le_one_left (Real.rpow_nonneg (by linarith) _)
      (ψ.allCoefficient_norm_le_one P)).trans_lt
        (Real.rpow_lt_one_of_one_lt_of_neg hN (by linarith))
  intro hz
  rw [← sub_eq_zero.mp hz,norm_one] at H
  exact (lt_irrefl _ H)

theorem idealEulerDeletion_halfplane_bounds (M : Ideal (𝓞 K)) {s : ℂ}
    (hs : (1/2 : ℝ) ≤ s.re) :
    ‖ψ.idealEulerDeletion M s‖ ≤ (2 : ℝ)^(HeckeIdealMobius.primeSupport K M).card ∧
      ‖(ψ.idealEulerDeletion M s)⁻¹‖ ≤ (4 : ℝ)^(HeckeIdealMobius.primeSupport K M).card := by
  have hl (P : Ideal (𝓞 K)) (hP : P ∈ HeckeIdealMobius.primeSupport K M) :
      ‖1-ψ.allCoefficient P*(Ideal.absNorm P : ℂ)^(-s)‖ ≤ 2 ∧
      ‖(1-ψ.allCoefficient P*(Ideal.absNorm P : ℂ)^(-s))⁻¹‖ ≤ 4 := by
    have hN : 2 ≤ (Ideal.absNorm P : ℝ) := by exact_mod_cast ideal_prime_support_norm_ge_two K hP
    simpa only [Complex.ofReal_natCast] using norm_one_sub_euler_ratio_bounds hN hs (ψ.allCoefficient_norm_le_one P)
  constructor
  · rw [idealEulerDeletion,norm_prod]
    calc
      _ ≤ ∏ _P ∈ HeckeIdealMobius.primeSupport K M, (2 : ℝ) :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun P hP => (hl P hP).1)
      _ = _ := by simp
  · rw [idealEulerDeletion,← Finset.prod_inv_distrib,norm_prod]
    calc
      _ ≤ ∏ _P ∈ HeckeIdealMobius.primeSupport K M, (4 : ℝ) :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun P hP => (hl P hP).2)
      _ = _ := by simp

end EvenIdealRayCharacter

theorem exists_idealEulerDeletion_subpower_bound
    (K : Type*) [Field K] [NumberField K] (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {f : Ideal (𝓞 K)} (ψ : EvenIdealRayCharacter K f)
      (M : Ideal (𝓞 K)), M ≠ ⊥ → ∀ s : ℂ, (1/2 : ℝ) ≤ s.re →
      ‖ψ.idealEulerDeletion M s‖ + ‖(ψ.idealEulerDeletion M s)⁻¹‖ ≤
        C*(Ideal.absNorm M : ℝ)^ε := by
  obtain ⟨C,hC,hbound⟩ := HeckeIdealMobius.prime_support_subsets_bound K (ε/2) (by positivity)
  refine ⟨C+C^2,by positivity,?_⟩
  intro f ψ M hM s hs
  have hN : 0 < (Ideal.absNorm M : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hM)
  have hN1 : 1 ≤ (Ideal.absNorm M : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hM)
  have H := hbound M hM
  obtain ⟨h0,h1⟩ := ψ.idealEulerDeletion_halfplane_bounds M hs
  have hu : ‖ψ.idealEulerDeletion M s‖ ≤ C*(Ideal.absNorm M : ℝ)^ε :=
    (h0.trans H).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)) hC.le)
  have hi : ‖(ψ.idealEulerDeletion M s)⁻¹‖ ≤ C^2*(Ideal.absNorm M : ℝ)^ε := by
    have hsq := (sq_le_sq₀ (by positivity) (by positivity)).mpr H
    have he : ((2 : ℝ)^(HeckeIdealMobius.primeSupport K M).card)^2 =
        (4 : ℝ)^(HeckeIdealMobius.primeSupport K M).card := by rw [← pow_mul, mul_comm _ 2, pow_mul]; norm_num
    have he' : ((Ideal.absNorm M : ℝ)^(ε/2))^2 = (Ideal.absNorm M : ℝ)^ε := by
      rw [← Real.rpow_mul_natCast hN.le]
      congr 1
      ring
    rw [he,mul_pow,he'] at hsq
    exact h1.trans hsq
  nlinarith

end
end ArtinMatthews.VaryingKummerAnalytic
