module

public import ArtinMatthews.PrincipalQuotientFourier
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
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


set_option backward.privateInPublic true
@[expose] public section

/-! A higher outer-modulus cancellation on genuine principal quotients.
The argument is support of the primitive lower Fourier transform. -/
namespace ArtinMatthews.SIntegerFourier

open scoped Classical
noncomputable section
variable {R : Type*} [CommRing R] [IsDomain R]

def principalHigherMixedSum (a b c : R)
    (ψ : AddChar (R ⧸ Ideal.span {(a * b) * c}) ℂ)
    (χ ξ : (R ⧸ Ideal.span {a}) → ℂ) (H : R) : ℂ :=
  ∑' v : R ⧸ Ideal.span {(a * b) * c},
    ξ (quotientReduction a b (quotientReduction (a * b) c v)) *
      ψ (Ideal.Quotient.mk _ H * v) *
      ∑' d : R ⧸ Ideal.span {a * b},
        χ (quotientReduction a b d) * ψ (-(quotientScale (a * b) c d * v))

theorem principalHigherMixedSum_eq_zero (a b c : R) (ha : a ≠ 0) (hc : c ≠ 0)
    (hab : a ∣ b) (ψ : AddChar (R ⧸ Ideal.span {(a * b) * c}) ℂ)
    (hψ : ψ.IsPrimitive) (χ ξ : (R ⧸ Ideal.span {a}) → ℂ) (hξ : ξ 0 = 0) (H : R) :
    principalHigherMixedSum a b c ψ χ ξ H = 0 := by
  unfold principalHigherMixedSum
  apply Eq.trans (b := ∑' _v : R ⧸ Ideal.span {(a * b) * c}, (0 : ℂ)) _ tsum_zero
  apply tsum_congr
  intro v
  obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective v
  have he : (∑' d : R ⧸ Ideal.span {a * b},
      χ (quotientReduction a b d) *
        ψ (-(quotientScale (a * b) c d * Ideal.Quotient.mk _ h))) =
      principalFourier a b (quotientLowerChar (a * b) c ψ) χ (-h) := by
    unfold principalFourier
    apply tsum_congr
    intro d
    obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective d
    congr 1
    rw [quotientScale_mk, ← map_mul, ← map_neg, ← map_mul, quotientLowerChar_mk]
    congr 2
    ring
  rw [he]
  by_cases hF : principalFourier a b (quotientLowerChar (a * b) c ψ) χ (-h) = 0
  · rw [hF, mul_zero]
  · have hd := principalFourier_support a b ha _
      (quotientLowerChar_primitive (a * b) c hc ψ hψ) χ (-h) hF
    have hd' : a ∣ h := dvd_trans hab (dvd_neg.mp hd)
    have hz : Ideal.Quotient.mk (Ideal.span {a}) h = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hd')
    change ξ (Ideal.Quotient.mk (Ideal.span {a}) h) * _ * _ = 0
    rw [hz, hξ, zero_mul, zero_mul]

end
end ArtinMatthews.SIntegerFourier
