module

public import ArtinMatthews.ProbeIdealGaussLifting
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import OAI.NumberTheory.DirichletL.Detector.Gauss
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! Literal congruence-defined local sums over arbitrary ideal-prime powers. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField IsDedekindDomain OAI.SevenEighths
open scoped NumberField BigOperators Classical
noncomputable section

variable (K : Type*) [Field K] [NumberField K]

def probeIdealScalarOne (P : HeightOneSpectrum (𝓞 K))
    (χ ξ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (n : ℕ) (h : 𝓞 K) : ℂ :=
  ∑' d : ((𝓞 K) ⧸ P.asIdeal), χ d *
    probeIdealGaussAt K P ξ (n + 1) (Nat.succ_pos n)
      (h - probeIdealUniformizer P ^ n * Quotient.out d)

theorem probeIdealScalarOne_eq (P : HeightOneSpectrum (𝓞 K))
    (χ ξ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (n : ℕ) (h : 𝓞 K) :
    probeIdealScalarOne K P χ ξ n h =
      χ⁻¹ (-1) * probeIdealTau K P χ *
        probeIdealGaussAt K P (ξ * χ⁻¹) (n + 1) (Nat.succ_pos n) h := by
  let : Field ((𝓞 K) ⧸ P.asIdeal) := Ideal.Quotient.field _
  let : Finite ((𝓞 K) ⧸ P.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient P.ne_bot
  let : Fintype ((𝓞 K) ⧸ P.asIdeal) := Fintype.ofFinite _
  have hτ : probeIdealTau K P χ = gaussSum χ (probeIdealResiduePhase K P) := by
    rw [probeIdealTau, tsum_fintype]
    rfl
  by_cases hd : h ∈ P.asIdeal ^ n
  · obtain ⟨a, ha⟩ := probeIdealUniformizer_approx P 1 n h hd
    have ha' : h - probeIdealUniformizer P ^ n * a ∈ P.asIdeal ^ (n + 1) := by
      simpa only [Nat.add_comm] using ha
    have hmk (d : ((𝓞 K) ⧸ P.asIdeal)) :
        Ideal.Quotient.mk P.asIdeal (a - Quotient.out d) =
          Ideal.Quotient.mk _ a - d := by rw [map_sub, Ideal.Quotient.mk_out]
    have hfreq (d : ((𝓞 K) ⧸ P.asIdeal)) :
        probeIdealGaussAt K P ξ (n + 1) (Nat.succ_pos n)
            (h - probeIdealUniformizer P ^ n * Quotient.out d) =
          probeIdealGaussAt K P ξ (n + 1) (Nat.succ_pos n)
            (probeIdealUniformizer P ^ n * (a - Quotient.out d)) := by
      apply probeIdealGaussAt_frequency_congr
      convert ha' using 1; ring
    have hs : probeIdealScalarOne K P χ ξ n h =
        (Ideal.absNorm P.asIdeal : ℂ) ^ n *
          ∑ d : ((𝓞 K) ⧸ P.asIdeal), χ d *
            ProbeGauss.frequencyGauss ξ (probeIdealResiduePhase K P)
              (Ideal.Quotient.mk _ a - d) := by
      unfold probeIdealScalarOne
      rw [tsum_fintype, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      rw [hfreq, probeIdealGaussAt_lift_residue, tsum_fintype]
      simp only [hmk, ProbeGauss.frequencyGauss]
      ring
    rw [hs, ProbeGauss.finite_gauss_convolution, hτ,
      probeIdealGaussAt_frequency_congr K P (ξ * χ⁻¹) (n + 1) (Nat.succ_pos n)
        h (probeIdealUniformizer P ^ n * a) ha',
      probeIdealGaussAt_lift_residue, tsum_fintype]
    unfold ProbeGauss.frequencyGauss
    ring
  · have hz (η : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (a : 𝓞 K)
        (ha : a ∉ P.asIdeal ^ n) :
        probeIdealGaussAt K P η (n + 1) (Nat.succ_pos n) a = 0 := by
      apply probeIdealGaussAt_zero_off_support
      simpa only [Nat.add_sub_cancel] using ha
    rw [hz _ h hd, mul_zero]
    unfold probeIdealScalarOne
    apply Eq.trans (b := ∑' _d : ((𝓞 K) ⧸ P.asIdeal), (0 : ℂ)) _ tsum_zero
    apply tsum_congr
    intro d
    have hnd : h - probeIdealUniformizer P ^ n * Quotient.out d ∉ P.asIdeal ^ n := by
      intro hh
      apply hd
      have he := (P.asIdeal ^ n).add_mem hh
        ((P.asIdeal ^ n).mul_mem_right (Quotient.out d) (probeIdealUniformizer_pow_mem P n))
      simpa only [sub_add_cancel] using he
    rw [hz _ _ hnd, mul_zero]

def probeIdealLocalCZero (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (n J : ℕ) : ℂ :=
  probeIdealGaussAt K P (χ ^ (n + 1)) (n + 1) (Nat.succ_pos n)
    (probeIdealUniformizer P ^ J)

def probeIdealLocalCOne (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (n J : ℕ) : ℂ :=
  ∑' d : ((𝓞 K) ⧸ P.asIdeal),
    if hd : probeIdealUniformizer P ^ J -
        probeIdealUniformizer P ^ (n + 1) * Quotient.out d ∈ P.asIdeal ^ 1 then
      χ d * probeIdealResidueGauss K P (χ ^ (n + 1)) (n + 1) (Nat.succ_pos n)
        (probeIdealDivideResidue P (n + 1) 1 _ hd)
    else 0

theorem probeIdealLocalCZero_eq (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (n J : ℕ) :
    probeIdealLocalCZero K P χ n J =
      if n ≤ J then (Ideal.absNorm P.asIdeal : ℂ) ^ n *
        probeIdealResidueTransform K P χ (n + 1)
          (probeIdealUniformizer P ^ (J - n)) else 0 := by
  simpa only [probeIdealLocalCZero, Nat.add_sub_cancel, probeIdealResidueTransform]
    using probeIdealGaussAt_prime_power K P (χ ^ (n + 1)) (n + 1) J (Nat.succ_pos n)

theorem probeIdealLocalCOne_zero (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (n : ℕ) :
    probeIdealLocalCOne K P χ n 0 = 0 := by
  unfold probeIdealLocalCOne
  apply Eq.trans (b := ∑' _d : ((𝓞 K) ⧸ P.asIdeal), (0 : ℂ)) _ tsum_zero
  apply tsum_congr
  intro d
  have hd : probeIdealUniformizer P ^ 0 -
      probeIdealUniformizer P ^ (n + 1) * Quotient.out d ∉ P.asIdeal ^ 1 := by
    intro hh
    have he := (P.asIdeal ^ 1).add_mem hh
      ((P.asIdeal ^ 1).mul_mem_right (Quotient.out d)
        ((probeIdealUniformizer_pow_mem_iff K P (n + 1) 1).mpr (by omega)))
    have h1 : (1 : 𝓞 K) ∈ P.asIdeal := by
      simpa only [sub_add_cancel, pow_zero, pow_one] using he
    exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  exact dite_eq_right hd

theorem probeIdealLocalCOne_succ (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (n J : ℕ) :
    probeIdealLocalCOne K P χ n (J + 1) =
      probeIdealScalarOne K P χ (χ ^ (n + 1)) n (probeIdealUniformizer P ^ J) := by
  unfold probeIdealLocalCOne probeIdealScalarOne
  apply tsum_congr
  intro d
  have he : probeIdealUniformizer P ^ (J + 1) -
      probeIdealUniformizer P ^ (n + 1) * Quotient.out d =
      probeIdealUniformizer P *
        (probeIdealUniformizer P ^ J - probeIdealUniformizer P ^ n * Quotient.out d) := by
    simp only [pow_succ']
    ring
  have hm : probeIdealUniformizer P *
      (probeIdealUniformizer P ^ J - probeIdealUniformizer P ^ n * Quotient.out d)
      ∈ P.asIdeal ^ 1 := by
    simpa only [pow_one] using P.asIdeal.mul_mem_right _ (probeIdealUniformizer_mem P)
  rw [he, dite_eq_left hm]
  have hdiv : probeIdealDivideResidue P (n + 1) 1
      (probeIdealUniformizer P *
        (probeIdealUniformizer P ^ J - probeIdealUniformizer P ^ n * Quotient.out d)) hm =
      Ideal.Quotient.mk (P.asIdeal ^ (n + 1))
        (probeIdealUniformizer P ^ J - probeIdealUniformizer P ^ n * Quotient.out d) := by
    simpa only [pow_one] using probeIdealDivideResidue_uniformizer_mul P (n + 1) 1
      (probeIdealUniformizer P ^ J - probeIdealUniformizer P ^ n * Quotient.out d)
      (by simpa only [pow_one] using hm)
  rw [hdiv, probeIdealResidueGauss_mk]

theorem probeIdealLocalCOne_eq (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (hχ : χ (-1) = 1) (n J : ℕ) :
    probeIdealLocalCOne K P χ n J =
      if n + 1 ≤ J then probeIdealTau K P χ *
        (Ideal.absNorm P.asIdeal : ℂ) ^ n *
        probeIdealResidueTransform K P χ n
          (probeIdealUniformizer P ^ (J - (n + 1))) else 0 := by
  cases J with
  | zero => rw [probeIdealLocalCOne_zero]; simp
  | succ J =>
    rw [probeIdealLocalCOne_succ, probeIdealScalarOne_eq, MulChar.inv_apply_eq_inv',
      hχ, inv_one, one_mul, pow_succ, mul_inv_cancel_right]
    by_cases hnJ : n ≤ J
    · rw [ite_eq_left (Nat.succ_le_succ hnJ)]
      have hpow : probeIdealUniformizer P ^ J =
          probeIdealUniformizer P ^ n * probeIdealUniformizer P ^ (J - n) := by
        rw [← pow_add, Nat.add_sub_of_le hnJ]
      rw [hpow, probeIdealGaussAt_lift_residue]
      simp only [Nat.succ_sub_succ_eq_sub, probeIdealResidueTransform]
      ring
    · rw [ite_eq_right (fun h => hnJ (Nat.succ_le_succ_iff.mp h))]
      have hm : probeIdealUniformizer P ^ J ∉ P.asIdeal ^ ((n + 1) - 1) := by
        simpa only [Nat.add_sub_cancel] using
          (fun hd => hnJ ((probeIdealUniformizer_pow_mem_iff K P J n).mp hd))
      rw [probeIdealGaussAt_zero_off_support K P _ (n + 1) (Nat.succ_pos n) _ hm, mul_zero]

end

end ArtinMatthews.VaryingKummerAnalytic
