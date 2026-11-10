module

public import ArtinMatthews.PrincipalOppositeFourier
public import ArtinMatthews.PrincipalQuotientFourier
public import ArtinMatthews.PrincipalQuotientFiber
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
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

/-! The finite source Fourier identity on principal quotients.  No
coprimality of the two moduli is used.  The support gate and its exact
fiber multiplicity are derived from primitive quotient Fourier lifting. -/
namespace ArtinMatthews.SIntegerFourier

open scoped Classical
noncomputable section
variable {R : Type*} [CommRing R] [IsDomain R]

def principalQuotientGauss (a b : R)
    (ψ : AddChar (R ⧸ Ideal.span {a * b}) ℂ)
    (f : R ⧸ Ideal.span {a} → ℂ) (r : R ⧸ Ideal.span {a}) : ℂ :=
  ∑' d : R ⧸ Ideal.span {a}, f d * quotientLowerChar a b ψ (r * d)

def principalSourceKernel (a b : R)
    (ψ : AddChar (R ⧸ Ideal.span {a * b}) ℂ)
    (f : R ⧸ Ideal.span {a} → ℂ) (g : R ⧸ Ideal.span {b} → ℂ) (h : R) : ℂ :=
  ∑' d : R ⧸ Ideal.span {a}, ∑' v : R ⧸ Ideal.span {b},
    if h - b * Quotient.out d ∈ Ideal.span {a} then
      f d * g v * ψ (Ideal.Quotient.mk _ ((h - b * Quotient.out d) * Quotient.out v))
    else 0

omit [IsDomain R] in
theorem principalQuotientGauss_phase (a b : R)
    (ψ : AddChar (R ⧸ Ideal.span {a * b}) ℂ) (h : R)
    (m : R ⧸ Ideal.span {a * b}) (d : R ⧸ Ideal.span {a}) :
    quotientLowerChar a b ψ (-(quotientReduction a b m) * d) *
        ψ (Ideal.Quotient.mk _ h * m) =
      ψ (Ideal.Quotient.mk _ (h - b * Quotient.out d) * m) := by
  obtain ⟨m, rfl⟩ := Ideal.Quotient.mk_surjective m
  have hd := Ideal.Quotient.mk_out d
  conv_lhs => rw [← hd]
  change ψ (Ideal.Quotient.mk (Ideal.span {a * b}) (b * (-m * Quotient.out d))) *
      ψ (Ideal.Quotient.mk _ (h * m)) =
    ψ (Ideal.Quotient.mk _ ((h - b * Quotient.out d) * m))
  rw [← AddChar.map_add_eq_mul, ← map_add]
  congr 2
  ring

theorem oppositeFourier_eq_gated (a b : R) (hb : b ≠ 0)
    [Finite (R ⧸ Ideal.span {b})] [Finite (R ⧸ Ideal.span {a * b})]
    (ψ : AddChar (R ⧸ Ideal.span {a * b}) ℂ) (hψ : ψ.IsPrimitive)
    (g : R ⧸ Ideal.span {b} → ℂ) (h : R) :
    oppositeFourier a b ψ g h =
      if h ∈ Ideal.span {a} then (Nat.card (R ⧸ Ideal.span {a}) : ℂ) *
        ∑' v : R ⧸ Ideal.span {b},
          g v * ψ (Ideal.Quotient.mk _ (h * Quotient.out v))
      else 0 := by
  by_cases hh : h ∈ Ideal.span {a}
  · rw [ite_eq_left hh]
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp hh
    rw [hq, oppositeFourier_lift, oppositeReduction_card_ker a b hb]
    congr 1
    apply tsum_congr
    intro v
    congr 1
    have hv := Ideal.Quotient.mk_out v
    conv_lhs => rw [← hv]
    change ψ (Ideal.Quotient.mk (Ideal.span {a * b}) (a * (q * Quotient.out v))) =
      ψ (Ideal.Quotient.mk _ (a * q * Quotient.out v))
    rw [mul_assoc]
  · rw [ite_eq_right hh]
    by_contra hn
    exact hh (Ideal.mem_span_singleton.mpr (oppositeFourier_support a b hb ψ hψ g h hn))

theorem principalSourceFiniteFourier (a b : R) (hb : b ≠ 0)
    [Finite (R ⧸ Ideal.span {a})] [Finite (R ⧸ Ideal.span {b})]
    [Finite (R ⧸ Ideal.span {a * b})]
    (ψ : AddChar (R ⧸ Ideal.span {a * b}) ℂ) (hψ : ψ.IsPrimitive)
    (f : R ⧸ Ideal.span {a} → ℂ) (g : R ⧸ Ideal.span {b} → ℂ) (h : R) :
    (∑' m : R ⧸ Ideal.span {a * b},
      principalQuotientGauss a b ψ f (-(quotientReduction a b m)) *
        g (oppositeReduction a b m) * ψ (Ideal.Quotient.mk _ h * m)) =
      (Nat.card (R ⧸ Ideal.span {a}) : ℂ) * principalSourceKernel a b ψ f g h := by
  unfold principalQuotientGauss
  simp_rw [← tsum_mul_right]
  have hswap (F : (R ⧸ Ideal.span {a * b}) → (R ⧸ Ideal.span {a}) → ℂ) :
      (∑' m, ∑' d, F m d) = ∑' d, ∑' m, F m d := by
    let : Fintype (R ⧸ Ideal.span {a * b}) := Fintype.ofFinite _
    let : Fintype (R ⧸ Ideal.span {a}) := Fintype.ofFinite _
    simp only [tsum_fintype]
    exact Finset.sum_comm
  rw [hswap]
  have hi (d : R ⧸ Ideal.span {a}) :
      (∑' m : R ⧸ Ideal.span {a * b},
        f d * quotientLowerChar a b ψ (-(quotientReduction a b m) * d) *
          g (oppositeReduction a b m) * ψ (Ideal.Quotient.mk _ h * m)) =
      f d * oppositeFourier a b ψ g (h - b * Quotient.out d) := by
    unfold oppositeFourier
    rw [← tsum_mul_left]
    apply tsum_congr
    intro m
    have he := principalQuotientGauss_phase a b ψ h m d
    rw [← he]
    ring
  simp_rw [hi, oppositeFourier_eq_gated a b hb ψ hψ]
  unfold principalSourceKernel
  rw [← tsum_mul_left]
  apply tsum_congr
  intro d
  split_ifs with hd
  · simp_rw [← tsum_mul_left]
    apply tsum_congr
    intro v
    ring
  · simp only [mul_zero, tsum_zero]

end
end ArtinMatthews.SIntegerFourier
