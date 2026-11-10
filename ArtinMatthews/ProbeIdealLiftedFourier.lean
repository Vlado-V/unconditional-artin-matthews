module

public import ArtinMatthews.VaryingKummerAnalyticIdealTraceCharacter
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
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! Fourier lifting on actual principal ideal quotients.  The lower additive
character is induced from the upper trace character; no compatibility between
independently chosen trace generators is presumed. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField
open scoped NumberField BigOperators Classical
noncomputable section

variable {K : Type*} [Field K]

def probeIdealReduction (a b : 𝓞 K) :
    ((𝓞 K) ⧸ Ideal.span {a * b}) →+* ((𝓞 K) ⧸ Ideal.span {a}) :=
  Ideal.Quotient.factor
    (Ideal.span_singleton_le_span_singleton.mpr (dvd_mul_right a b))

theorem probeIdealReduction_surjective (a b : 𝓞 K) :
    Function.Surjective (probeIdealReduction a b) := Ideal.Quotient.factor_surjective _

def probeIdealScale (a b : 𝓞 K) :
    ((𝓞 K) ⧸ Ideal.span {a}) →+ ((𝓞 K) ⧸ Ideal.span {a * b}) :=
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

theorem probeIdealScale_mk (a b x : 𝓞 K) :
    probeIdealScale a b (Ideal.Quotient.mk (Ideal.span {a}) x) =
      Ideal.Quotient.mk (Ideal.span {a * b}) (b * x) := rfl

theorem probeIdealScale_injective (a b : 𝓞 K) (hb : b ≠ 0) :
    Function.Injective (probeIdealScale a b) := by
  apply (probeIdealScale a b).ker_eq_bot_iff.mp
  apply bot_unique
  intro x hx
  change probeIdealScale a b x = 0 at hx
  change x = 0
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [probeIdealScale_mk, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hx
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply Ideal.mem_span_singleton.mpr
  have hx' : b * a ∣ b * x := by simpa only [mul_comm a b] using hx
  exact (mul_dvd_mul_iff_left hb).mp hx'

def probeIdealLowerChar (a b : 𝓞 K)
    (ψ : AddChar ((𝓞 K) ⧸ Ideal.span {a * b}) ℂ) :
    AddChar ((𝓞 K) ⧸ Ideal.span {a}) ℂ :=
  ψ.compAddMonoidHom (probeIdealScale a b)

theorem probeIdealLowerChar_mk (a b x : 𝓞 K)
    (ψ : AddChar ((𝓞 K) ⧸ Ideal.span {a * b}) ℂ) :
    probeIdealLowerChar a b ψ (Ideal.Quotient.mk (Ideal.span {a}) x) =
      ψ (Ideal.Quotient.mk (Ideal.span {a * b}) (b * x)) := rfl

theorem probeIdealLowerChar_primitive (a b : 𝓞 K) (hb : b ≠ 0)
    (ψ : AddChar ((𝓞 K) ⧸ Ideal.span {a * b}) ℂ) (hψ : ψ.IsPrimitive) :
    (probeIdealLowerChar a b ψ).IsPrimitive := by
  intro x hx he
  obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hn : Ideal.Quotient.mk (Ideal.span {a * b}) (b * d) ≠ 0 := by
    intro hz
    apply hx
    apply probeIdealScale_injective a b hb
    simpa only [probeIdealScale_mk, map_zero] using hz
  apply hψ hn
  ext y
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  have ht := congrArg
    (fun χ : AddChar ((𝓞 K) ⧸ Ideal.span {a}) ℂ =>
      χ (Ideal.Quotient.mk (Ideal.span {a}) y)) he
  simpa only [AddChar.mulShift_apply, ← map_mul,
    probeIdealLowerChar_mk, mul_assoc, AddChar.one_apply] using ht

variable (K) [NumberField K]

private theorem probeQuotientFinite (a : 𝓞 K) (ha : a ≠ 0) :
    Finite ((𝓞 K) ⧸ Ideal.span {a}) :=
  Ring.HasFiniteQuotients.finiteQuotient (Ideal.span_singleton_eq_bot.not.mpr ha)

def probeIdealFourier (a b : 𝓞 K) (ha : a ≠ 0) (hb : b ≠ 0)
    (F : ((𝓞 K) ⧸ Ideal.span {a}) → ℂ) (h : 𝓞 K) : ℂ :=
  ∑' x : ((𝓞 K) ⧸ Ideal.span {a * b}),
    F (probeIdealReduction a b x) *
      idealTraceAddChar K (Ideal.span {a * b})
        (Ideal.span_singleton_eq_bot.not.mpr (mul_ne_zero ha hb))
        (Ideal.Quotient.mk _ h * x)

theorem probeIdealFourier_shift (a b : 𝓞 K) (ha : a ≠ 0) (hb : b ≠ 0)
    (F : ((𝓞 K) ⧸ Ideal.span {a}) → ℂ) (h t : 𝓞 K) :
    probeIdealFourier K a b ha hb F h =
      idealTraceAddChar K (Ideal.span {a * b})
        (Ideal.span_singleton_eq_bot.not.mpr (mul_ne_zero ha hb))
        (Ideal.Quotient.mk _ (h * a * t)) * probeIdealFourier K a b ha hb F h := by
  let q : ((𝓞 K) ⧸ Ideal.span {a * b}) := Ideal.Quotient.mk _ (a * t)
  have hq : probeIdealReduction a b q = 0 := by
    change Ideal.Quotient.mk (Ideal.span {a}) (a * t) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_span_singleton.mpr ⟨t, rfl⟩)
  unfold probeIdealFourier
  conv_lhs => rw [← (Equiv.addRight q).tsum_eq]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro x
  change F (probeIdealReduction a b (x + q)) *
    idealTraceAddChar K (Ideal.span {a * b}) _
      (Ideal.Quotient.mk _ h * (x + q)) = _
  simp only [map_add, hq, add_zero, mul_add, AddChar.map_add_eq_mul]
  have he : Ideal.Quotient.mk (Ideal.span {a * b}) h * q =
      Ideal.Quotient.mk _ (h * a * t) := by
    dsimp [q]
    rw [← map_mul]
    congr 1
    ring
  rw [he]
  ring

theorem probeIdealFourier_support (a b : 𝓞 K) (ha : a ≠ 0) (hb : b ≠ 0)
    (F : ((𝓞 K) ⧸ Ideal.span {a}) → ℂ) (h : 𝓞 K)
    (hF : probeIdealFourier K a b ha hb F h ≠ 0) : b ∣ h := by
  have hphase (t : 𝓞 K) :
      idealTraceAddChar K (Ideal.span {a * b})
        (Ideal.span_singleton_eq_bot.not.mpr (mul_ne_zero ha hb))
        (Ideal.Quotient.mk _ (h * a * t)) = 1 := by
    apply mul_right_cancel₀ hF
    rw [one_mul, ← probeIdealFourier_shift]
  have hz : Ideal.Quotient.mk (Ideal.span {a * b}) (h * a) = 0 := by
    by_contra hn
    apply idealTraceAddChar_isPrimitive K (Ideal.span {a * b})
      (Ideal.span_singleton_eq_bot.not.mpr (mul_ne_zero ha hb)) hn
    ext x
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective x
    simpa only [AddChar.mulShift_apply, ← map_mul, AddChar.one_apply] using hphase t
  have hd := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz)
  have hd' : a * b ∣ a * h := by simpa only [mul_comm h a] using hd
  exact (mul_dvd_mul_iff_left ha).mp hd'

theorem probeIdealFourier_zero_off_support (a b : 𝓞 K)
    (ha : a ≠ 0) (hb : b ≠ 0) (F : ((𝓞 K) ⧸ Ideal.span {a}) → ℂ)
    (h : 𝓞 K) (hd : ¬ b ∣ h) : probeIdealFourier K a b ha hb F h = 0 := by
  by_contra hF
  exact hd (probeIdealFourier_support K a b ha hb F h hF)

theorem probeIdealReduction_kernel_card (a b : 𝓞 K) (ha : a ≠ 0) :
    Nat.card (probeIdealReduction a b).toAddMonoidHom.ker =
      Ideal.absNorm (Ideal.span {b}) := by
  have hc := AddSubgroup.card_ker_mul_card_of_surjective
    (f := (probeIdealReduction a b).toAddMonoidHom)
    (probeIdealReduction_surjective a b)
  have hnorm (x : 𝓞 K) : Nat.card ((𝓞 K) ⧸ Ideal.span {x}) =
      Ideal.absNorm (Ideal.span {x}) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hmul : Ideal.absNorm (Ideal.span {a * b}) =
      Ideal.absNorm (Ideal.span {a}) * Ideal.absNorm (Ideal.span {b}) := by
    rw [← Ideal.span_singleton_mul_span_singleton, map_mul]
  rw [hnorm, hnorm, hmul] at hc
  have hpos : 0 < Ideal.absNorm (Ideal.span {a}) :=
    Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr ha))
  exact Nat.eq_of_mul_eq_mul_right hpos (hc.trans (Nat.mul_comm _ _))

private theorem probe_finite_tsum_pullback {R S : Type*} [AddGroup R] [AddGroup S]
    [Finite R] [Finite S] (f : R →+ S) (hf : Function.Surjective f) (F : S → ℂ) :
    (∑' x : R, F (f x)) = (Nat.card f.ker : ℂ) * ∑' y : S, F y := by
  let : Fintype R := Fintype.ofFinite _
  let : Fintype S := Fintype.ofFinite _
  let : Fintype f.ker := Fintype.ofFinite _
  rw [tsum_fintype, tsum_fintype, ← Fintype.sum_fiberwise' f F]
  have hc (y : S) : Fintype.card {x : R // f x = y} = Fintype.card f.ker :=
    Fintype.card_congr (AddMonoidHom.fiberEquivKerOfSurjective hf y)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hc,
    Nat.card_eq_fintype_card]
  rw [Finset.mul_sum]

theorem probeIdealFourier_lift (a b : 𝓞 K) (ha : a ≠ 0) (hb : b ≠ 0)
    (F : ((𝓞 K) ⧸ Ideal.span {a}) → ℂ) (k : 𝓞 K) :
    probeIdealFourier K a b ha hb F (b * k) =
      (Ideal.absNorm (Ideal.span {b}) : ℂ) *
        ∑' x : ((𝓞 K) ⧸ Ideal.span {a}), F x *
          probeIdealLowerChar a b
            (idealTraceAddChar K (Ideal.span {a * b})
              (Ideal.span_singleton_eq_bot.not.mpr (mul_ne_zero ha hb)))
            (Ideal.Quotient.mk _ k * x) := by
  let : Finite ((𝓞 K) ⧸ Ideal.span {a}) := probeQuotientFinite K a ha
  let : Finite ((𝓞 K) ⧸ Ideal.span {a * b}) :=
    probeQuotientFinite K (a * b) (mul_ne_zero ha hb)
  unfold probeIdealFourier
  calc
    _ = ∑' x : ((𝓞 K) ⧸ Ideal.span {a * b}), F (probeIdealReduction a b x) *
        probeIdealLowerChar a b
          (idealTraceAddChar K (Ideal.span {a * b})
            (Ideal.span_singleton_eq_bot.not.mpr (mul_ne_zero ha hb)))
          (Ideal.Quotient.mk _ k * probeIdealReduction a b x) := by
      apply tsum_congr
      intro x
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      congr 1
      change _ = probeIdealLowerChar a b _ (Ideal.Quotient.mk _ k * Ideal.Quotient.mk _ x)
      rw [← map_mul (Ideal.Quotient.mk (Ideal.span {a})) k x,
        probeIdealLowerChar_mk, ← map_mul, mul_assoc]
    _ = _ := by
      have he := probe_finite_tsum_pullback (probeIdealReduction a b).toAddMonoidHom
        (probeIdealReduction_surjective a b)
        (fun x => F x * probeIdealLowerChar a b
          (idealTraceAddChar K (Ideal.span {a * b})
            (Ideal.span_singleton_eq_bot.not.mpr (mul_ne_zero ha hb)))
          (Ideal.Quotient.mk _ k * x))
      rw [probeIdealReduction_kernel_card K a b ha] at he
      exact he

end

end ArtinMatthews.VaryingKummerAnalytic
