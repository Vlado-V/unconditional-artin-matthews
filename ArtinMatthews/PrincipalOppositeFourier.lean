module

public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import ArtinMatthews.PrincipalQuotientFourier
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Basify
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

/-! Fourier lifting onto the second factor of a genuine principal
quotient. The order of the product is retained for the source double sum. -/
namespace ArtinMatthews.SIntegerFourier

open scoped Classical
noncomputable section
variable {R : Type*} [CommRing R] [IsDomain R]

def oppositeReduction (a b : R) :
    (R ⧸ Ideal.span {a * b}) →+* (R ⧸ Ideal.span {b}) :=
  Ideal.Quotient.factor
    (Ideal.span_singleton_le_span_singleton.mpr (dvd_mul_left b a))

omit [IsDomain R] in
theorem oppositeReduction_surjective (a b : R) : Function.Surjective (oppositeReduction a b) :=
  Ideal.Quotient.factor_surjective _

def oppositeScale (a b : R) : (R ⧸ Ideal.span {b}) →+ (R ⧸ Ideal.span {a * b}) :=
  QuotientAddGroup.lift (Ideal.span {b}).toAddSubgroup
    { toFun := fun x => Ideal.Quotient.mk (Ideal.span {a * b}) (a * x)
      map_zero' := by simp
      map_add' := by simp [mul_add] }
    (by
      intro x hx
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton.mp hx
      apply Ideal.mem_span_singleton.mpr
      exact ⟨y, by ring⟩)

omit [IsDomain R] in
theorem oppositeScale_mk (a b x : R) :
    oppositeScale a b (Ideal.Quotient.mk (Ideal.span {b}) x) =
      Ideal.Quotient.mk (Ideal.span {a * b}) (a * x) := rfl

def oppositeLowerChar (a b : R) (ψ : AddChar (R ⧸ Ideal.span {a * b}) ℂ) :
    AddChar (R ⧸ Ideal.span {b}) ℂ := ψ.compAddMonoidHom (oppositeScale a b)

omit [IsDomain R] in
theorem oppositeLowerChar_mk (a b x : R) (ψ : AddChar (R ⧸ Ideal.span {a * b}) ℂ) :
    oppositeLowerChar a b ψ (Ideal.Quotient.mk (Ideal.span {b}) x) =
      ψ (Ideal.Quotient.mk (Ideal.span {a * b}) (a * x)) := rfl

def oppositeFourier (a b : R) (ψ : AddChar (R ⧸ Ideal.span {a * b}) ℂ)
    (F : (R ⧸ Ideal.span {b}) → ℂ) (h : R) : ℂ :=
  ∑' x : R ⧸ Ideal.span {a * b},
    F (oppositeReduction a b x) * ψ (Ideal.Quotient.mk _ h * x)

omit [IsDomain R] in
theorem oppositeFourier_shift (a b : R) (ψ : AddChar (R ⧸ Ideal.span {a * b}) ℂ)
    (F : (R ⧸ Ideal.span {b}) → ℂ) (h t : R) :
    oppositeFourier a b ψ F h =
      ψ (Ideal.Quotient.mk _ (h * b * t)) * oppositeFourier a b ψ F h := by
  let q : R ⧸ Ideal.span {a * b} := Ideal.Quotient.mk _ (b * t)
  have hq : oppositeReduction a b q = 0 := by
    change Ideal.Quotient.mk (Ideal.span {b}) (b * t) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr ⟨t, rfl⟩)
  unfold oppositeFourier
  conv_lhs => rw [← (Equiv.addRight q).tsum_eq]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro x
  change F (oppositeReduction a b (x + q)) * ψ (Ideal.Quotient.mk _ h * (x + q)) = _
  simp only [map_add, hq, add_zero, mul_add, AddChar.map_add_eq_mul]
  have he : Ideal.Quotient.mk (Ideal.span {a * b}) h * q =
      Ideal.Quotient.mk _ (h * b * t) := by
    dsimp [q]
    rw [← map_mul]
    congr 1
    ring
  rw [he]
  ring

theorem oppositeFourier_support (a b : R) (hb : b ≠ 0)
    (ψ : AddChar (R ⧸ Ideal.span {a * b}) ℂ) (hψ : ψ.IsPrimitive)
    (F : (R ⧸ Ideal.span {b}) → ℂ) (h : R)
    (hF : oppositeFourier a b ψ F h ≠ 0) : a ∣ h := by
  have hphase (t : R) : ψ (Ideal.Quotient.mk _ (h * b * t)) = 1 := by
    apply mul_right_cancel₀ hF
    rw [one_mul, ← oppositeFourier_shift]
  have hz : Ideal.Quotient.mk (Ideal.span {a * b}) (h * b) = 0 := by
    by_contra hn
    apply hψ hn
    ext x
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective x
    simpa only [AddChar.mulShift_apply, ← map_mul, AddChar.one_apply] using hphase t
  have hd := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz)
  have hd' : b * a ∣ b * h := by simpa only [mul_comm a b, mul_comm h b] using hd
  exact (mul_dvd_mul_iff_left hb).mp hd'

omit [IsDomain R] in
theorem oppositeFourier_lift (a b : R) [Finite (R ⧸ Ideal.span {b})]
    [Finite (R ⧸ Ideal.span {a * b})] (ψ : AddChar (R ⧸ Ideal.span {a * b}) ℂ)
    (F : (R ⧸ Ideal.span {b}) → ℂ) (h : R) :
    oppositeFourier a b ψ F (a * h) =
      (Nat.card (oppositeReduction a b).toAddMonoidHom.ker : ℂ) *
        ∑' x : R ⧸ Ideal.span {b}, F x * oppositeLowerChar a b ψ (Ideal.Quotient.mk _ h * x) := by
  unfold oppositeFourier
  calc
    _ = ∑' x : R ⧸ Ideal.span {a * b}, F (oppositeReduction a b x) *
        oppositeLowerChar a b ψ (Ideal.Quotient.mk _ h * oppositeReduction a b x) := by
      apply tsum_congr
      intro x
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      congr 1
      change _ = oppositeLowerChar a b ψ (Ideal.Quotient.mk _ h * Ideal.Quotient.mk _ x)
      rw [← map_mul (Ideal.Quotient.mk (Ideal.span {b})) h x, oppositeLowerChar_mk,
        ← map_mul, mul_assoc]
    _ = _ := finite_tsum_pullback (oppositeReduction a b).toAddMonoidHom
      (oppositeReduction_surjective a b)
      (fun x : R ⧸ Ideal.span {b} => F x * oppositeLowerChar a b ψ (Ideal.Quotient.mk _ h * x))

end
end ArtinMatthews.SIntegerFourier
