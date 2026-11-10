module

public import ArtinMatthews.ProbePrimeLocalScalars
public import ArtinMatthews.ProbePrimePowerLifting
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


set_option backward.privateInPublic true
@[expose] public section

/-! The literal higher-outer local sums.  The congruence indicator is removed
by the proved exact-quotient lift, and the resulting double sum is killed by
translation on the outer prime-power quotient. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField
open scoped NumberField BigOperators Classical
noncomputable section

variable (K : Type*) [Field K] [NumberField K]

def probePrimeLocalHigher (p : 𝓞 K) (hp : p ≠ 0)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (n m J : ℕ) : ℂ :=
  ∑' d : ((𝓞 K) ⧸ Ideal.span {p * p ^ m}),
    if hd : p ^ (m + 1) ∣ p ^ J - p ^ (n + 1) * Quotient.out d then
      (χ ^ (m + 1)) (probeIdealReduction p (p ^ m) d) *
        probePrimePowerGauss K p hp (χ ^ (n + 1)) n
          (probeLocalExactQuotient K _ (p ^ (m + 1)) hd)
    else 0

theorem probePrimeLocalHigher_lift (p : 𝓞 K) (hp : p ≠ 0)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (n m J : ℕ) :
    probePrimeLocalHigher K p hp χ n m J =
      ((Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (m + 1))⁻¹ *
        ∑' d : ((𝓞 K) ⧸ Ideal.span {p * p ^ m}),
          (χ ^ (m + 1)) (probeIdealReduction p (p ^ m) d) *
            probePrimePowerGauss K p hp (χ ^ (n + 1)) (n + (m + 1))
              (p ^ J - p ^ (n + 1) * Quotient.out d) := by
  unfold probePrimeLocalHigher
  rw [← tsum_mul_left]
  apply tsum_congr
  intro d
  let H := p ^ J - p ^ (n + 1) * Quotient.out d
  have he := probePrimePowerGauss_exactQuotient K p hp (χ ^ (n + 1)) n (m + 1) H
    (fun hd => ⟨probeLocalExactQuotient K H (p ^ (m + 1)) hd,
      probeLocalExactQuotient_spec K H (p ^ (m + 1)) hd⟩)
  by_cases hd : p ^ (m + 1) ∣ H
  · rw [dite_eq_left hd] at he ⊢
    rw [he]
    ring
  · rw [dite_eq_right hd] at he ⊢
    linear_combination (χ ^ (m + 1)) (probeIdealReduction p (p ^ m) d) * he

private theorem probe_primitive_transport {A B : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) (ψ : AddChar B ℂ) (hψ : ψ.IsPrimitive) :
    (ψ.compAddMonoidHom e.toAddMonoidHom).IsPrimitive := by
  intro x hx he
  have hex : e x ≠ 0 := by
    intro h
    apply hx
    apply e.injective
    simpa only [map_zero] using h
  apply hψ hex
  ext y
  obtain ⟨y, rfl⟩ := e.surjective y
  have ht := congrArg (fun φ : AddChar A ℂ => φ y) he
  change ψ (e (x * y)) = 1 at ht
  simpa only [map_mul, AddChar.mulShift_apply, AddChar.one_apply] using ht

theorem probePrimeLocalHigher_eq_zero (p : 𝓞 K) (hp : Prime p)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (n m J : ℕ) (hm : 0 < m) :
    probePrimeLocalHigher K p hp.ne_zero χ n m J = 0 := by
  have he : Ideal.span {p * p ^ (n + (m + 1))} =
      Ideal.span {(p * p ^ m) * p ^ (n + 1)} := by
    rw [show n + (m + 1) = m + (n + 1) by omega, pow_add, mul_assoc]
  let e := Ideal.quotEquivOfEq he
  have hemk (x : 𝓞 K) :
      e (Ideal.Quotient.mk (Ideal.span {p * p ^ (n + (m + 1))}) x) =
        Ideal.Quotient.mk (Ideal.span {(p * p ^ m) * p ^ (n + 1)}) x :=
    Ideal.quotEquivOfEq_mk he x
  have heinv (x : 𝓞 K) :
      e.symm (Ideal.Quotient.mk (Ideal.span {(p * p ^ m) * p ^ (n + 1)}) x) =
        Ideal.Quotient.mk (Ideal.span {p * p ^ (n + (m + 1))}) x := by
    apply e.injective
    rw [e.apply_symm_apply, hemk]
  let ψ : AddChar ((𝓞 K) ⧸ Ideal.span {(p * p ^ m) * p ^ (n + 1)}) ℂ :=
    (probePrimePowerPhase K p hp.ne_zero (n + (m + 1))).compAddMonoidHom
      e.symm.toAddMonoidHom
  have hψ : ψ.IsPrimitive := probe_primitive_transport e.symm _
    (probePrimePowerPhase_primitive K p hp.ne_zero (n + (m + 1)))
  let : Finite ((𝓞 K) ⧸ Ideal.span {p * p ^ m}) :=
    Ring.HasFiniteQuotients.finiteQuotient
      (Ideal.span_singleton_eq_bot.not.mpr (mul_ne_zero hp.ne_zero (pow_ne_zero m hp.ne_zero)))
  let : Fintype ((𝓞 K) ⧸ Ideal.span {p * p ^ m}) := Fintype.ofFinite _
  let : Finite ((𝓞 K) ⧸ Ideal.span {(p * p ^ m) * p ^ (n + 1)}) :=
    Ring.HasFiniteQuotients.finiteQuotient (Ideal.span_singleton_eq_bot.not.mpr
      (mul_ne_zero (mul_ne_zero hp.ne_zero (pow_ne_zero m hp.ne_zero))
        (pow_ne_zero (n + 1) hp.ne_zero)))
  let : Fintype ((𝓞 K) ⧸ Ideal.span {(p * p ^ m) * p ^ (n + 1)}) := Fintype.ofFinite _
  have hG (d : ((𝓞 K) ⧸ Ideal.span {p * p ^ m})) :
      probePrimePowerGauss K p hp.ne_zero (χ ^ (n + 1)) (n + (m + 1))
          (p ^ J - p ^ (n + 1) * Quotient.out d) =
        ∑' v : ((𝓞 K) ⧸ Ideal.span {(p * p ^ m) * p ^ (n + 1)}),
          (χ ^ (n + 1)) (probeIdealReduction p (p ^ m)
            (probeIdealReduction (p * p ^ m) (p ^ (n + 1)) v)) *
          ψ (Ideal.Quotient.mk _ (p ^ J - p ^ (n + 1) * Quotient.out d) * v) := by
    unfold probePrimePowerGauss probeQuotientFourier
    rw [← e.symm.toEquiv.tsum_eq]
    apply tsum_congr
    intro v
    obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective v
    change (χ ^ (n + 1)) (probeIdealReduction p (p ^ (n + (m + 1)))
      (e.symm (Ideal.Quotient.mk _ v))) *
      probePrimePowerPhase K p hp.ne_zero (n + (m + 1))
        (Ideal.Quotient.mk _ _ * e.symm (Ideal.Quotient.mk _ v)) = _
    rw [heinv]
    change (χ ^ (n + 1)) (Ideal.Quotient.mk (Ideal.span {p}) v) * _ =
      (χ ^ (n + 1)) (Ideal.Quotient.mk (Ideal.span {p}) v) * _
    congr 1
  have hphase (d : ((𝓞 K) ⧸ Ideal.span {p * p ^ m}))
      (v : ((𝓞 K) ⧸ Ideal.span {(p * p ^ m) * p ^ (n + 1)})) :
      ψ (Ideal.Quotient.mk _ (p ^ J - p ^ (n + 1) * Quotient.out d) * v) =
        ψ (Ideal.Quotient.mk _ (p ^ J) * v) *
          ψ (-(probeIdealScale (p * p ^ m) (p ^ (n + 1)) d * v)) := by
    have hd : probeIdealScale (p * p ^ m) (p ^ (n + 1)) d =
        Ideal.Quotient.mk _ (p ^ (n + 1) * Quotient.out d) := by
      conv_lhs => rw [show d = Ideal.Quotient.mk _ (Quotient.out d) from
        (Ideal.Quotient.mk_out d).symm]
      exact probeIdealScale_mk _ _ _
    rw [hd, map_sub, sub_mul, sub_eq_add_neg, AddChar.map_add_eq_mul]
  have hdouble :
      (∑' d : ((𝓞 K) ⧸ Ideal.span {p * p ^ m}),
          (χ ^ (m + 1)) (probeIdealReduction p (p ^ m) d) *
            probePrimePowerGauss K p hp.ne_zero (χ ^ (n + 1)) (n + (m + 1))
              (p ^ J - p ^ (n + 1) * Quotient.out d)) =
        probeHigherOuterMixedSum p (p ^ (n + 1)) m (χ ^ (m + 1))
          (χ ^ (n + 1)) ψ (p ^ J) := by
    simp only [hG, probeHigherOuterMixedSum, tsum_fintype, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v _
    apply Finset.sum_congr rfl
    intro d _
    rw [hphase]
    ring
  rw [probePrimeLocalHigher_lift, hdouble,
    probeHigherOuterMixedSum_eq_zero p (p ^ (n + 1)) hp
      (pow_ne_zero (n + 1) hp.ne_zero) m hm _ _ ψ hψ, mul_zero]

end

end ArtinMatthews.VaryingKummerAnalytic
