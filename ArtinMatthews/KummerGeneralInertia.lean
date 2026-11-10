module

public import Mathlib.NumberTheory.NumberField.Basic
public import ArtinMatthews.KummerRootReduction
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
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


set_option backward.privateInPublic true
@[expose] public section

/-! Inertia fixes integral radicals of base-field elements away from the
exponent and the radicand. The base radicand is an arbitrary algebraic
integer, not restricted to a rational integer. -/
namespace ArtinMatthews
open scoped NumberField
noncomputable section

variable {L : Type*} [Field L] [NumberField L]
attribute [local instance] Ideal.Quotient.field

omit [NumberField L] in
theorem integral_powerRoots_eq_of_reduction_eq {n : ℕ} (hn : 0 < n)
    (Q : Ideal (𝓞 L)) [Q.IsMaximal] (hnQ : (n : 𝓞 L) ∉ Q)
    (x y : 𝓞 L) (hxy : x^n=y^n) (hyQ : Ideal.Quotient.mk Q y ≠ 0)
    (hred : Ideal.Quotient.mk Q x=Ideal.Quotient.mk Q y) : x=y := by
  have hy0 : (y:L) ≠ 0 := by
    intro hy
    apply hyQ
    rw [show y=0 from Subtype.ext hy,map_zero]
  let u : L := (x:L)/(y:L)
  have hun : u^n=1 := by
    dsimp only [u]
    rw [div_pow,show (x:L)^n=(y:L)^n from congrArg (fun z : 𝓞 L => (z:L)) hxy,
      div_self (pow_ne_zero n hy0)]
  let z : 𝓞 L := ⟨u,powerRoot_isIntegral hn (a := 1) (by simpa using hun)⟩
  have hzn : z^n=1 := Subtype.ext hun
  have hzmul : z*y=x := Subtype.ext (div_mul_cancel₀ (x:L) hy0)
  have hzred : Ideal.Quotient.mk Q z=1 := by
    apply mul_right_cancel₀ hyQ
    rw [← map_mul,hzmul,hred,one_mul]
  have hz1 := power_unity_eq_one_of_reduction_eq_one Q hnQ hzn hzred
  have hu1 : u=1 := congrArg (fun z : 𝓞 L => (z:L)) hz1
  exact Subtype.ext ((div_eq_one_iff_eq hy0).mp hu1)

variable {F : Type*} [Field F] [NumberField F] [Algebra F L]

omit [NumberField F] [NumberField L] in
theorem inertia_fixes_integral_base_powerRoot {n : ℕ} (hn : 0 < n)
    (Q : Ideal (𝓞 L)) [Q.IsMaximal] (hnQ : (n : 𝓞 L) ∉ Q)
    (a : 𝓞 F) (haQ : algebraMap (𝓞 F) (𝓞 L) a ∉ Q)
    (x : 𝓞 L) (hx : x^n=algebraMap (𝓞 F) (𝓞 L) a)
    (σ : Gal(L/F)) (hσ : σ ∈ Q.inertia Gal(L/F)) : σ • x=x := by
  have hpow : (σ • x)^n=x^n := by
    apply Subtype.ext
    change (σ (x:L))^n=(x:L)^n
    rw [← map_pow]
    have hh : (x:L)^n=algebraMap F L (a:F) :=
      congrArg (fun z : 𝓞 L => (z:L)) hx
    rw [hh,σ.commutes]
  have hxQ : Ideal.Quotient.mk Q x ≠ 0 := by
    intro hz
    apply haQ
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [← hx,map_pow,hz,zero_pow hn.ne']
  have hred : Ideal.Quotient.mk Q (σ • x)=Ideal.Quotient.mk Q x := by
    rw [Ideal.Quotient.eq]
    exact hσ x
  exact integral_powerRoots_eq_of_reduction_eq hn Q hnQ (σ • x) x hpow hxQ hred

end
end ArtinMatthews
