module

public import ArtinMatthews.KummerSplittingGaloisField
public import Mathlib.RingTheory.RamificationInertia.Ramification
public import ArtinMatthews.KummerRootReduction
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
public import Mathlib.NumberTheory.RamificationInertia.Galois
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

/-! The actual Kummer field has trivial inertia away from the integer
radicand and the exponent. The proof uses its two explicit generators. -/

namespace ArtinMatthews
open scoped NumberField

noncomputable def kummerCyclotomicRoot (q : ℕ) (a : ℤ) : primeKummerField q a :=
  ⟨primeCyclotomicRoot q,
    primeCyclotomicField_le_primeKummerField q a (primeCyclotomicRoot_mem q)⟩

noncomputable def kummerRadicalRoot (q : ℕ) (a : ℤ) : primeKummerField q a :=
  ⟨primeRadicalRoot q a, primeRadicalRoot_mem_primeKummerField q a⟩

theorem kummerCyclotomicRoot_pow {q : ℕ} (hq : 0 < q) (a : ℤ) :
    kummerCyclotomicRoot q a ^ q = 1 := by
  apply Subtype.ext
  exact primeCyclotomicRoot_pow hq

theorem kummerRadicalRoot_pow {q : ℕ} (hq : 0 < q) (a : ℤ) :
    kummerRadicalRoot q a ^ q = (a : primeKummerField q a) := by
  apply Subtype.ext
  exact primeRadicalRoot_pow hq a

/-- Fixing the two actual generators forces an automorphism to be identity. -/
theorem primeKummer_aut_eq_one {q : ℕ} {a : ℤ}
    (σ : Gal(primeKummerField q a/ℚ))
    (hζ : σ (kummerCyclotomicRoot q a) = kummerCyclotomicRoot q a)
    (hα : σ (kummerRadicalRoot q a) = kummerRadicalRoot q a) : σ = 1 := by
  have heq : σ.toAlgHom = (1 : Gal(primeKummerField q a/ℚ)).toAlgHom := by
    apply IntermediateField.algHom_ext_of_eq_adjoin ℚ (primeKummerField_eq_adjoin q a)
    intro x hx
    rcases hx with hx | hx
    · have hx' := Set.mem_singleton_iff.mp hx
      subst x
      exact hζ
    · have hx' := Set.mem_singleton_iff.mp hx
      subst x
      exact hα
  exact AlgEquiv.ext (fun x => AlgHom.congr_fun heq x)

section GeneralInertia
variable {K : Type*} [Field K] [NumberField K]
attribute [local instance] Ideal.Quotient.field

/-- Inertia fixes each integral radical whose exponent and radicand have
nonzero reduction. -/
theorem inertia_fixes_powerRoot {q : ℕ} (hq : 0 < q)
    (Q : Ideal (𝓞 K)) [Q.IsMaximal] (hqQ : (q : 𝓞 K) ∉ Q)
    {a : ℤ} (haQ : (a : 𝓞 K) ∉ Q) {x : K} (hx : x ^ q = (a : K))
    (σ : Gal(K/ℚ)) (hσ : σ ∈ Q.inertia Gal(K/ℚ)) : σ x = x := by
  let r : 𝓞 K := ⟨x, powerRoot_isIntegral hq hx⟩
  have hr : r ^ q = (a : 𝓞 K) := by apply Subtype.ext; exact hx
  have hσr : (σ • r) ^ q = (a : 𝓞 K) := by
    apply Subtype.ext
    change (σ x) ^ q = (a : K)
    rw [← map_pow, hx, map_intCast]
  have hrQ : Ideal.Quotient.mk Q r ≠ 0 := by
    intro hz
    apply haQ
    apply (Ideal.Quotient.eq_zero_iff_mem (I := Q)).mp
    rw [← hr, map_pow, hz, zero_pow hq.ne']
  have hred : Ideal.Quotient.mk Q (σ • r) = Ideal.Quotient.mk Q r := by
    rw [Ideal.Quotient.eq]
    exact hσ r
  have hh := powerRoot_eq_of_reduction_eq hq Q hqQ hσr hr hrQ hred
  exact congrArg (fun z : 𝓞 K => (z : K)) hh
end GeneralInertia

/-- Away from q and a, every element of the actual inertia group is identity. -/
theorem primeKummer_inertia_eq_bot {q : ℕ} {a : ℤ} [NeZero q] [NeZero a]
    (Q : Ideal (𝓞 (primeKummerField q a))) [Q.IsMaximal]
    (hqQ : (q : 𝓞 (primeKummerField q a)) ∉ Q)
    (haQ : (a : 𝓞 (primeKummerField q a)) ∉ Q) :
    Q.inertia Gal(primeKummerField q a/ℚ) = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro σ hσ
  change σ = 1
  apply primeKummer_aut_eq_one
  · exact inertia_fixes_powerRoot (NeZero.pos q) Q hqQ
      (a := 1) (by simpa using (Q.ne_top_iff_one).mp Ideal.IsPrime.ne_top')
      (by simpa using kummerCyclotomicRoot_pow (NeZero.pos q) a) σ hσ
  · exact inertia_fixes_powerRoot (NeZero.pos q) Q hqQ haQ
      (kummerRadicalRoot_pow (NeZero.pos q) a) σ hσ

/-- Consequently the actual ramification index is one, with exactly the
exceptional rational divisors of a q removed. -/
theorem primeKummer_ramificationIdx_eq_one {q : ℕ} {a : ℤ} [NeZero q] [NeZero a]
    (Q : Ideal (𝓞 (primeKummerField q a))) [Q.IsMaximal]
    (hqQ : (q : 𝓞 (primeKummerField q a)) ∉ Q)
    (haQ : (a : 𝓞 (primeKummerField q a)) ∉ Q) :
    Q.ramificationIdx ℤ = 1 := by
  have hI := Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(primeKummerField q a/ℚ))
    (Q.under ℤ) Q
  rw [primeKummer_inertia_eq_bot Q hqQ haQ, Nat.card_unique, Ideal.ramificationIdxIn_eq_ramificationIdx (Q.under ℤ) Q
      Gal(primeKummerField q a/ℚ)] at hI
  exact hI.symm

end ArtinMatthews
