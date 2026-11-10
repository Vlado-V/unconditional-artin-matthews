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

/-! The missing-modulus cases of the literal local coefficient.  The zero
modulus is a one-point sum of weight one; positive outer modulus still uses
the zero-extended multiplicative character. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField
open scoped NumberField BigOperators Classical
noncomputable section

variable (K : Type*) [Field K] [NumberField K]

def probePrimeLocalBothAbsent : ℂ := ∑ _ : Unit, (1 : ℂ)

theorem probePrimeLocalBothAbsent_eq_one : probePrimeLocalBothAbsent = 1 := by
  simp [probePrimeLocalBothAbsent]

def probePrimeLocalInnerAbsent (p : 𝓞 K)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (m J : ℕ) : ℂ :=
  ∑' d : ((𝓞 K) ⧸ Ideal.span {p * p ^ m}),
    if d = Ideal.Quotient.mk _ (p ^ J) then
      (χ ^ (m + 1)) (probeIdealReduction p (p ^ m) d) else 0

theorem probePrimeLocalInnerAbsent_eq (p : 𝓞 K) (hp : Prime p)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (m J : ℕ) :
    probePrimeLocalInnerAbsent K p χ m J = if J = 0 then 1 else 0 := by
  let : (Ideal.span {p} : Ideal (𝓞 K)).IsMaximal :=
    ((Ideal.span_singleton_prime hp.ne_zero).mpr hp).isMaximal
      (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero)
  let : Field ((𝓞 K) ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  unfold probePrimeLocalInnerAbsent
  rw [tsum_eq_single (Ideal.Quotient.mk (Ideal.span {p * p ^ m}) (p ^ J))]
  · rw [ite_eq_left rfl]
    change (χ ^ (m + 1)) (Ideal.Quotient.mk (Ideal.span {p}) (p ^ J)) = _
    cases J with
    | zero => simp
    | succ J =>
        have hz : Ideal.Quotient.mk (Ideal.span {p}) (p ^ (J + 1)) = 0 := by
          rw [map_pow]
          have hpz : Ideal.Quotient.mk (Ideal.span {p}) p = 0 :=
            Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self p)
          rw [hpz, zero_pow (Nat.succ_ne_zero J)]
        rw [hz, MulChar.map_zero, ite_eq_right (Nat.succ_ne_zero J)]
  · intro d hd
    exact ite_eq_right hd

end

end ArtinMatthews.VaryingKummerAnalytic
