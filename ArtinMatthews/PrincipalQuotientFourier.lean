module

public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
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

/-! Generic Fourier lifting on actual principal quotients. The lower
character is induced through the proved quotient scale; no character
compatibility is supplied in place of the lifting argument. -/

namespace ArtinMatthews.SIntegerFourier


open scoped BigOperators Classical
noncomputable section

variable {R : Type*} [CommRing R] [IsDomain R]

def quotientReduction (a b : R) :
    ((R) ⧸ Ideal.span {a * b}) →+* ((R) ⧸ Ideal.span {a}) :=
  Ideal.Quotient.factor
    (Ideal.span_singleton_le_span_singleton.mpr (dvd_mul_right a b))

omit [IsDomain R] in
theorem quotientReduction_surjective (a b : R) :
    Function.Surjective (quotientReduction a b) := Ideal.Quotient.factor_surjective _

def quotientScale (a b : R) :
    ((R) ⧸ Ideal.span {a}) →+ ((R) ⧸ Ideal.span {a * b}) :=
  QuotientAddGroup.lift (Ideal.span {a}).toAddSubgroup
    { toFun := fun x => Ideal.Quotient.mk (Ideal.span {a * b}) (b * x)
      map_zero' := by simp
      map_add' := by simp [mul_add] }
    (by
      intro x hx
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton.mp hx
      apply Ideal.mem_span_singleton.mpr
      exact ⟨y, by ring⟩)

omit [IsDomain R] in
theorem quotientScale_mk (a b x : R) :
    quotientScale a b (Ideal.Quotient.mk (Ideal.span {a}) x) =
      Ideal.Quotient.mk (Ideal.span {a * b}) (b * x) := rfl

theorem quotientScale_injective (a b : R) (hb : b ≠ 0) :
    Function.Injective (quotientScale a b) := by
  apply (quotientScale a b).ker_eq_bot_iff.mp
  apply bot_unique
  intro x hx
  change quotientScale a b x = 0 at hx
  change x = 0
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [quotientScale_mk, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hx
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply Ideal.mem_span_singleton.mpr
  have hx' : b * a ∣ b * x := by simpa only [mul_comm a b] using hx
  exact (mul_dvd_mul_iff_left hb).mp hx'

def quotientLowerChar (a b : R)
    (ψ : AddChar ((R) ⧸ Ideal.span {a * b}) ℂ) :
    AddChar ((R) ⧸ Ideal.span {a}) ℂ :=
  ψ.compAddMonoidHom (quotientScale a b)

omit [IsDomain R] in
theorem quotientLowerChar_mk (a b x : R)
    (ψ : AddChar ((R) ⧸ Ideal.span {a * b}) ℂ) :
    quotientLowerChar a b ψ (Ideal.Quotient.mk (Ideal.span {a}) x) =
      ψ (Ideal.Quotient.mk (Ideal.span {a * b}) (b * x)) := rfl

theorem quotientLowerChar_primitive (a b : R) (hb : b ≠ 0)
    (ψ : AddChar ((R) ⧸ Ideal.span {a * b}) ℂ) (hψ : ψ.IsPrimitive) :
    (quotientLowerChar a b ψ).IsPrimitive := by
  intro x hx he
  obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hn : Ideal.Quotient.mk (Ideal.span {a * b}) (b * d) ≠ 0 := by
    intro hz
    apply hx
    apply quotientScale_injective a b hb
    simpa only [quotientScale_mk, map_zero] using hz
  apply hψ hn
  ext y
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  have ht := congrArg
    (fun χ : AddChar ((R) ⧸ Ideal.span {a}) ℂ =>
      χ (Ideal.Quotient.mk (Ideal.span {a}) y)) he
  simpa only [AddChar.mulShift_apply, ← map_mul,
    quotientLowerChar_mk, mul_assoc, AddChar.one_apply] using ht

def principalFourier (a b : R) (ψ : AddChar (R ⧸ Ideal.span {a * b}) ℂ)
    (F : (R ⧸ Ideal.span {a}) → ℂ) (h : R) : ℂ :=
  ∑' x : R ⧸ Ideal.span {a * b},
    F (quotientReduction a b x) * ψ (Ideal.Quotient.mk _ h * x)

omit [IsDomain R] in
theorem principalFourier_shift (a b : R) (ψ : AddChar (R ⧸ Ideal.span {a * b}) ℂ)
    (F : (R ⧸ Ideal.span {a}) → ℂ) (h t : R) :
    principalFourier a b ψ F h =
      ψ (Ideal.Quotient.mk _ (h * a * t)) * principalFourier a b ψ F h := by
  let q : R ⧸ Ideal.span {a * b} := Ideal.Quotient.mk _ (a * t)
  have hq : quotientReduction a b q = 0 := by
    change Ideal.Quotient.mk (Ideal.span {a}) (a * t) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr ⟨t, rfl⟩)
  unfold principalFourier
  conv_lhs => rw [← (Equiv.addRight q).tsum_eq]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro x
  change F (quotientReduction a b (x + q)) * ψ (Ideal.Quotient.mk _ h * (x + q)) = _
  simp only [map_add, hq, add_zero, mul_add, AddChar.map_add_eq_mul]
  have he : Ideal.Quotient.mk (Ideal.span {a * b}) h * q =
      Ideal.Quotient.mk _ (h * a * t) := by
    dsimp [q]
    rw [← map_mul]
    congr 1
    ring
  rw [he]
  ring

theorem principalFourier_support (a b : R) (ha : a ≠ 0)
    (ψ : AddChar (R ⧸ Ideal.span {a * b}) ℂ) (hψ : ψ.IsPrimitive)
    (F : (R ⧸ Ideal.span {a}) → ℂ) (h : R)
    (hF : principalFourier a b ψ F h ≠ 0) : b ∣ h := by
  have hphase (t : R) : ψ (Ideal.Quotient.mk _ (h * a * t)) = 1 := by
    apply mul_right_cancel₀ hF
    rw [one_mul, ← principalFourier_shift]
  have hz : Ideal.Quotient.mk (Ideal.span {a * b}) (h * a) = 0 := by
    by_contra hn
    apply hψ hn
    ext x
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective x
    simpa only [AddChar.mulShift_apply, ← map_mul, AddChar.one_apply] using hphase t
  have hd := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz)
  have hd' : a * b ∣ a * h := by simpa only [mul_comm h a] using hd
  exact (mul_dvd_mul_iff_left ha).mp hd'

theorem principalFourier_zero_off_support (a b : R) (ha : a ≠ 0)
    (ψ : AddChar (R ⧸ Ideal.span {a * b}) ℂ) (hψ : ψ.IsPrimitive)
    (F : (R ⧸ Ideal.span {a}) → ℂ) (h : R) (hd : ¬ b ∣ h) :
    principalFourier a b ψ F h = 0 := by
  by_contra hF
  exact hd (principalFourier_support a b ha ψ hψ F h hF)

omit [IsDomain R] in
theorem finite_tsum_pullback {A B : Type*} [AddGroup A] [AddGroup B] [Finite A] [Finite B]
    (f : A →+ B) (hf : Function.Surjective f) (F : B → ℂ) :
    (∑' x : A, F (f x)) = (Nat.card f.ker : ℂ) * ∑' y : B, F y := by
  let : Fintype A := Fintype.ofFinite _
  let : Fintype B := Fintype.ofFinite _
  let : Fintype f.ker := Fintype.ofFinite _
  rw [tsum_fintype, tsum_fintype, ← Fintype.sum_fiberwise' f F]
  have hc (y : B) : Fintype.card {x : A // f x = y} = Fintype.card f.ker :=
    Fintype.card_congr (AddMonoidHom.fiberEquivKerOfSurjective hf y)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hc, Nat.card_eq_fintype_card]
  rw [Finset.mul_sum]

omit [IsDomain R] in
theorem principalFourier_lift (a b : R) [Finite (R ⧸ Ideal.span {a})]
    [Finite (R ⧸ Ideal.span {a * b})]
    (ψ : AddChar (R ⧸ Ideal.span {a * b}) ℂ)
    (F : (R ⧸ Ideal.span {a}) → ℂ) (k : R) :
    principalFourier a b ψ F (b * k) =
      (Nat.card (quotientReduction a b).toAddMonoidHom.ker : ℂ) *
        ∑' x : R ⧸ Ideal.span {a}, F x * quotientLowerChar a b ψ (Ideal.Quotient.mk _ k * x) := by
  unfold principalFourier
  calc
    _ = ∑' x : R ⧸ Ideal.span {a * b}, F (quotientReduction a b x) *
        quotientLowerChar a b ψ (Ideal.Quotient.mk _ k * quotientReduction a b x) := by
      apply tsum_congr
      intro x
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      congr 1
      change _ = quotientLowerChar a b ψ (Ideal.Quotient.mk _ k * Ideal.Quotient.mk _ x)
      rw [← map_mul (Ideal.Quotient.mk (Ideal.span {a})) k x, quotientLowerChar_mk,
        ← map_mul, mul_assoc]
    _ = _ := finite_tsum_pullback (quotientReduction a b).toAddMonoidHom
      (quotientReduction_surjective a b)
      (fun x => F x * quotientLowerChar a b ψ (Ideal.Quotient.mk _ k * x))

end
end ArtinMatthews.SIntegerFourier

