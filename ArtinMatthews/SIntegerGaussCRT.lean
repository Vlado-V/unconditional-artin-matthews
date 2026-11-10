module

public import ArtinMatthews.SIntegerGaussCRTPhase
public import ArtinMatthews.SIntegerFiniteQuotients
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
public import Mathlib.NumberTheory.SelbergSieve
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

/-! Normalized source Gauss CRT in the actually constructed S-integer
ring. Norms are literal finite quotient cardinalities and the character
cross factors, including masked zeroth powers, remain exact. -/
namespace ArtinMatthews.SIntegerQuotient

open NumberField OAI.IdealGaussCRT ArtinMatthews.SIntegerPrincipalization
open ArtinMatthews.StandardAdelic
open scoped NumberField Classical BigOperators
noncomputable section
variable {K : Type} [Field K] [NumberField K]
variable (S₀ : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))

def sourceGaussScalar (a : PrincipalIntegerRing S₀) (ha : a ≠ 0)
    (χ : MulChar ((PrincipalIntegerRing S₀) ⧸ Ideal.span {a}) ℂ) : ℂ :=
  ∑' x : (PrincipalIntegerRing S₀) ⧸ Ideal.span {a},
    χ x * sIntegerQuotientPhase K (principalizingSet S₀) a ha x

def sourceProductGauss (a b : PrincipalIntegerRing S₀) (ha : a ≠ 0) (hb : b ≠ 0)
    (χa : MulChar ((PrincipalIntegerRing S₀) ⧸ Ideal.span {a}) ℂ)
    (χb : MulChar ((PrincipalIntegerRing S₀) ⧸ Ideal.span {b}) ℂ) : ℂ :=
  ∑' x : (PrincipalIntegerRing S₀) ⧸ (Ideal.span {a} * Ideal.span {b}),
    χa (Ideal.Quotient.factor Ideal.mul_le_left x) *
      χb (Ideal.Quotient.factor Ideal.mul_le_right x) * sourceProductPhase S₀ a b ha hb x

theorem sourceProductGauss_eq (a b : PrincipalIntegerRing S₀) (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : IsCoprime (Ideal.span {a}) (Ideal.span {b}))
    (χa : MulChar ((PrincipalIntegerRing S₀) ⧸ Ideal.span {a}) ℂ)
    (χb : MulChar ((PrincipalIntegerRing S₀) ⧸ Ideal.span {b}) ℂ) :
    sourceProductGauss S₀ a b ha hb χa χb =
      χa (Ideal.Quotient.mk _ b) * χb (Ideal.Quotient.mk _ a) *
        sourceGaussScalar S₀ a ha χa * sourceGaussScalar S₀ b hb χb := by
  let : Finite ((PrincipalIntegerRing S₀) ⧸ Ideal.span {a}) := principal_element_quotient_finite S₀ a ha
  let : Finite ((PrincipalIntegerRing S₀) ⧸ Ideal.span {b}) := principal_element_quotient_finite S₀ b hb
  let : Finite ((PrincipalIntegerRing S₀) ⧸ (Ideal.span {a} * Ideal.span {b})) :=
    principal_ideal_quotient_finite S₀ _ (mul_ne_zero
      (Ideal.span_singleton_eq_bot.not.mpr ha) (Ideal.span_singleton_eq_bot.not.mpr hb))
  let : Fintype ((PrincipalIntegerRing S₀) ⧸ Ideal.span {a}) := Fintype.ofFinite _
  let : Fintype ((PrincipalIntegerRing S₀) ⧸ Ideal.span {b}) := Fintype.ofFinite _
  let : Fintype ((PrincipalIntegerRing S₀) ⧸ (Ideal.span {a} * Ideal.span {b})) := Fintype.ofFinite _
  obtain ⟨u, v, huv⟩ := bezout_of_principal_coprime hab
  have H := gauss_sum_ideal_crt (Ideal.span {a}) (Ideal.span {b})
    (principal_coprime_of_bezout huv) χa χb (sourceProductPhase S₀ a b ha hb)
  rw [sourceProductPhase_left S₀ a b u v ha hb huv,
    sourceProductPhase_right S₀ a b u v ha hb huv,
    gauss_shift_bezout_left huv, gauss_shift_bezout_right huv] at H
  unfold sourceProductGauss sourceGaussScalar
  simp only [tsum_fintype]
  unfold gaussSum at H
  calc
    _ = _ := H
    _ = _ := by ring

def sourceQuotientNorm (a : PrincipalIntegerRing S₀) : ℕ :=
  Nat.card ((PrincipalIntegerRing S₀) ⧸ Ideal.span {a})

theorem sourceQuotientNorm_mul (a b : PrincipalIntegerRing S₀)
    (hab : IsCoprime (Ideal.span {a}) (Ideal.span {b})) :
    sourceQuotientNorm S₀ (a * b) = sourceQuotientNorm S₀ a * sourceQuotientNorm S₀ b := by
  unfold sourceQuotientNorm
  rw [← Ideal.span_singleton_mul_span_singleton,
    Nat.card_congr (Ideal.quotientMulEquivQuotientProd (Ideal.span {a}) (Ideal.span {b}) hab).toEquiv,
    Nat.card_prod]

def sourceGamma (a : PrincipalIntegerRing S₀) (ha : a ≠ 0)
    (χ : MulChar ((PrincipalIntegerRing S₀) ⧸ Ideal.span {a}) ℂ) : ℂ :=
  sourceGaussScalar S₀ a ha χ / (Real.sqrt (sourceQuotientNorm S₀ a) : ℂ)

def sourceProductGamma (a b : PrincipalIntegerRing S₀) (ha : a ≠ 0) (hb : b ≠ 0)
    (χa : MulChar ((PrincipalIntegerRing S₀) ⧸ Ideal.span {a}) ℂ)
    (χb : MulChar ((PrincipalIntegerRing S₀) ⧸ Ideal.span {b}) ℂ) : ℂ :=
  sourceProductGauss S₀ a b ha hb χa χb / (Real.sqrt (sourceQuotientNorm S₀ (a*b)) : ℂ)

theorem sourceGamma_crt (a b : PrincipalIntegerRing S₀) (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : IsCoprime (Ideal.span {a}) (Ideal.span {b}))
    (χa : MulChar ((PrincipalIntegerRing S₀) ⧸ Ideal.span {a}) ℂ)
    (χb : MulChar ((PrincipalIntegerRing S₀) ⧸ Ideal.span {b}) ℂ) :
    sourceProductGamma S₀ a b ha hb χa χb =
      χa (Ideal.Quotient.mk _ b) * χb (Ideal.Quotient.mk _ a) *
        sourceGamma S₀ a ha χa * sourceGamma S₀ b hb χb := by
  have hn : (Real.sqrt (sourceQuotientNorm S₀ (a*b)) : ℂ) =
      (Real.sqrt (sourceQuotientNorm S₀ a) : ℂ) * (Real.sqrt (sourceQuotientNorm S₀ b) : ℂ) := by
    have hr : Real.sqrt (sourceQuotientNorm S₀ (a*b) : ℝ) =
        Real.sqrt (sourceQuotientNorm S₀ a : ℝ) * Real.sqrt (sourceQuotientNorm S₀ b : ℝ) := by
      rw [sourceQuotientNorm_mul S₀ a b hab, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _)]
    exact_mod_cast hr
  unfold sourceProductGamma sourceGamma
  rw [sourceProductGauss_eq S₀ a b ha hb hab χa χb, hn]
  simp only [div_eq_mul_inv, mul_inv]
  ring

theorem sourceGamma_crt_pow (a b : PrincipalIntegerRing S₀) (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : IsCoprime (Ideal.span {a}) (Ideal.span {b}))
    (χa : MulChar ((PrincipalIntegerRing S₀) ⧸ Ideal.span {a}) ℂ)
    (χb : MulChar ((PrincipalIntegerRing S₀) ⧸ Ideal.span {b}) ℂ) (j : ℕ) :
    sourceProductGamma S₀ a b ha hb (χa^j) (χb^j) =
      (χa (Ideal.Quotient.mk _ b))^j * (χb (Ideal.Quotient.mk _ a))^j *
        sourceGamma S₀ a ha (χa^j) * sourceGamma S₀ b hb (χb^j) := by
  rw [sourceGamma_crt S₀ a b ha hb hab]
  obtain ⟨u, v, huv⟩ := bezout_of_principal_coprime hab
  have hba : IsUnit (Ideal.Quotient.mk (Ideal.span {a}) b) :=
    IsUnit.of_mul_eq_one_right (Ideal.Quotient.mk _ v)
      (by simpa only [mul_comm] using bezout_inverse_left huv)
  have hab' : IsUnit (Ideal.Quotient.mk (Ideal.span {b}) a) :=
    IsUnit.of_mul_eq_one_right (Ideal.Quotient.mk _ u)
      (by simpa only [mul_comm] using bezout_inverse_right huv)
  obtain ⟨ub, hub⟩ := hba
  obtain ⟨ua, hua⟩ := hab'
  rw [← hub, ← hua, χa.pow_apply_coe, χb.pow_apply_coe]

end
end ArtinMatthews.SIntegerQuotient
