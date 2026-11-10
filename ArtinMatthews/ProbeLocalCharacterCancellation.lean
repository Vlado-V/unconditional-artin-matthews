module

public import ArtinMatthews.ProbeIdealLiftedFourier
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
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
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


set_option backward.privateInPublic true
@[expose] public section

/-! Translation cancellation for the actual finite local quotients.  The
additive character may be the trace character or a proved primitive character
induced from a higher quotient. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField
open scoped NumberField BigOperators Classical
noncomputable section

variable {K : Type*} [Field K]

def probeQuotientFourier (a b : 𝓞 K)
    (ψ : AddChar ((𝓞 K) ⧸ Ideal.span {a * b}) ℂ)
    (F : ((𝓞 K) ⧸ Ideal.span {a}) → ℂ) (h : 𝓞 K) : ℂ :=
  ∑' x : ((𝓞 K) ⧸ Ideal.span {a * b}),
    F (probeIdealReduction a b x) * ψ (Ideal.Quotient.mk _ h * x)

theorem probeQuotientFourier_shift (a b : 𝓞 K)
    (ψ : AddChar ((𝓞 K) ⧸ Ideal.span {a * b}) ℂ)
    (F : ((𝓞 K) ⧸ Ideal.span {a}) → ℂ) (h t : 𝓞 K) :
    probeQuotientFourier a b ψ F h =
      ψ (Ideal.Quotient.mk _ (h * a * t)) * probeQuotientFourier a b ψ F h := by
  let q : ((𝓞 K) ⧸ Ideal.span {a * b}) := Ideal.Quotient.mk _ (a * t)
  have hq : probeIdealReduction a b q = 0 := by
    change Ideal.Quotient.mk (Ideal.span {a}) (a * t) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_span_singleton.mpr ⟨t, rfl⟩)
  unfold probeQuotientFourier
  conv_lhs => rw [← (Equiv.addRight q).tsum_eq]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro x
  change F (probeIdealReduction a b (x + q)) *
    ψ (Ideal.Quotient.mk _ h * (x + q)) = _
  simp only [map_add, hq, add_zero, mul_add, AddChar.map_add_eq_mul]
  have he : Ideal.Quotient.mk (Ideal.span {a * b}) h * q =
      Ideal.Quotient.mk _ (h * a * t) := by
    dsimp [q]
    rw [← map_mul]
    congr 1
    ring
  rw [he]
  ring

theorem probeQuotientFourier_support (a b : 𝓞 K) (ha : a ≠ 0)
    (ψ : AddChar ((𝓞 K) ⧸ Ideal.span {a * b}) ℂ) (hψ : ψ.IsPrimitive)
    (F : ((𝓞 K) ⧸ Ideal.span {a}) → ℂ) (h : 𝓞 K)
    (hF : probeQuotientFourier a b ψ F h ≠ 0) : b ∣ h := by
  have hphase (t : 𝓞 K) : ψ (Ideal.Quotient.mk _ (h * a * t)) = 1 := by
    apply mul_right_cancel₀ hF
    rw [one_mul, ← probeQuotientFourier_shift]
  have hz : Ideal.Quotient.mk (Ideal.span {a * b}) (h * a) = 0 := by
    by_contra hn
    apply hψ hn
    ext x
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective x
    simpa only [AddChar.mulShift_apply, ← map_mul, AddChar.one_apply] using hphase t
  have hd := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz)
  have hd' : a * b ∣ a * h := by simpa only [mul_comm h a] using hd
  exact (mul_dvd_mul_iff_left ha).mp hd'

theorem probeQuotientFourier_zero_off_support (a b : 𝓞 K) (ha : a ≠ 0)
    (ψ : AddChar ((𝓞 K) ⧸ Ideal.span {a * b}) ℂ) (hψ : ψ.IsPrimitive)
    (F : ((𝓞 K) ⧸ Ideal.span {a}) → ℂ) (h : 𝓞 K) (hd : ¬ b ∣ h) :
    probeQuotientFourier a b ψ F h = 0 := by
  by_contra hF
  exact hd (probeQuotientFourier_support a b ha ψ hψ F h hF)

theorem probeIdealScale_mul_reduction (a b : 𝓞 K)
    (d : ((𝓞 K) ⧸ Ideal.span {a})) (v : ((𝓞 K) ⧸ Ideal.span {a * b})) :
    probeIdealScale a b d * v =
      probeIdealScale a b (d * probeIdealReduction a b v) := by
  obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective d
  obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective v
  change Ideal.Quotient.mk _ (b * d) * Ideal.Quotient.mk _ v =
    probeIdealScale a b (Ideal.Quotient.mk _ d * Ideal.Quotient.mk _ v)
  rw [← map_mul (Ideal.Quotient.mk (Ideal.span {a})) d v, probeIdealScale_mk,
    ← map_mul, mul_assoc]

variable [NumberField K]

theorem probeHigherOuterFourier_annihilated (p : 𝓞 K) (hp : Prime p)
    (χ ξ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ)
    (n : ℕ) (hn : 0 < n)
    (ψ : AddChar ((𝓞 K) ⧸ Ideal.span {p * p ^ n}) ℂ) (hψ : ψ.IsPrimitive)
    (m : 𝓞 K) :
    ξ (Ideal.Quotient.mk _ m) * probeQuotientFourier p (p ^ n) ψ χ (-m) = 0 := by
  let : (Ideal.span {p} : Ideal (𝓞 K)).IsMaximal :=
    ((Ideal.span_singleton_prime hp.ne_zero).mpr hp).isMaximal
      (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero)
  let : Field ((𝓞 K) ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  by_cases hF : probeQuotientFourier p (p ^ n) ψ χ (-m) = 0
  · rw [hF, mul_zero]
  · have hdiv := probeQuotientFourier_support p (p ^ n) hp.ne_zero ψ hψ χ (-m) hF
    have hpm : p ∣ m := dvd_neg.mp
      ((dvd_pow_self p (Nat.ne_of_gt hn)).trans hdiv)
    have hz : Ideal.Quotient.mk (Ideal.span {p}) m = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hpm)
    rw [hz, MulChar.map_zero, zero_mul]

def probeHigherOuterMixedSum (p b : 𝓞 K) (n : ℕ)
    (χ ξ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ)
    (ψ : AddChar ((𝓞 K) ⧸ Ideal.span {(p * p ^ n) * b}) ℂ) (H : 𝓞 K) : ℂ :=
  ∑' v : ((𝓞 K) ⧸ Ideal.span {(p * p ^ n) * b}),
    ξ (probeIdealReduction p (p ^ n) (probeIdealReduction (p * p ^ n) b v)) *
      ψ (Ideal.Quotient.mk _ H * v) *
      ∑' d : ((𝓞 K) ⧸ Ideal.span {p * p ^ n}),
        χ (probeIdealReduction p (p ^ n) d) * ψ (-(probeIdealScale (p * p ^ n) b d * v))

theorem probeHigherOuterMixedSum_eq_zero (p b : 𝓞 K) (hp : Prime p) (hb : b ≠ 0)
    (n : ℕ) (hn : 0 < n) (χ ξ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ)
    (ψ : AddChar ((𝓞 K) ⧸ Ideal.span {(p * p ^ n) * b}) ℂ)
    (hψ : ψ.IsPrimitive) (H : 𝓞 K) :
    probeHigherOuterMixedSum p b n χ ξ ψ H = 0 := by
  unfold probeHigherOuterMixedSum
  apply Eq.trans (b := ∑' _v : ((𝓞 K) ⧸ Ideal.span {(p * p ^ n) * b}), (0 : ℂ))
    _ tsum_zero
  apply tsum_congr
  intro v
  obtain ⟨m, rfl⟩ := Ideal.Quotient.mk_surjective v
  have he : (∑' d : ((𝓞 K) ⧸ Ideal.span {p * p ^ n}),
      χ (probeIdealReduction p (p ^ n) d) *
        ψ (-(probeIdealScale (p * p ^ n) b d * Ideal.Quotient.mk _ m))) =
      probeQuotientFourier p (p ^ n)
        (probeIdealLowerChar (p * p ^ n) b ψ) χ (-m) := by
    unfold probeQuotientFourier
    apply tsum_congr
    intro d
    obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective d
    congr 1
    rw [probeIdealScale_mk, ← map_mul, ← map_neg]
    change ψ (Ideal.Quotient.mk _ (-(b * d * m))) =
      probeIdealLowerChar (p * p ^ n) b ψ
        (Ideal.Quotient.mk _ (-m) * Ideal.Quotient.mk _ d)
    rw [← map_mul, probeIdealLowerChar_mk]
    congr 2
    ring
  rw [he]
  have hz := probeHigherOuterFourier_annihilated p hp χ ξ n hn
    (probeIdealLowerChar (p * p ^ n) b ψ)
    (probeIdealLowerChar_primitive (p * p ^ n) b hb ψ hψ) m
  change ξ (Ideal.Quotient.mk _ m) * _ * _ = 0
  linear_combination ψ (Ideal.Quotient.mk _ H * Ideal.Quotient.mk _ m) * hz

end

end ArtinMatthews.VaryingKummerAnalytic
