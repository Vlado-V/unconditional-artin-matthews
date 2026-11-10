module

public import ArtinMatthews.CubicFrobeniusIntegral
public import ArtinMatthews.Index
public import ArtinMatthews.KummerSplittingGaloisField
public import ArtinMatthews.KummerRootReduction
public import ArtinMatthews.KummerSplittingInertia
public import ArtinMatthews.PowerResidues
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

/-! The actual varying-exponent Frobenius criterion for the concrete Kummer
field, together with its degree-one residue-field consequence. -/

namespace ArtinMatthews
open scoped NumberField

section GeneralFrobenius
variable {K : Type*} [Field K] [NumberField K] [IsGalois ℚ K]
attribute [local instance] Ideal.Quotient.field

/-- Identity arithmetic Frobenius forces the actual residue field to have p
rather than a higher power of p elements. -/
theorem IntegralFrobeniusData.residue_card_of_frobenius_eq_one
    {p : ℕ} [Fact p.Prime] (D : IntegralFrobeniusData K p)
    (hF : D.frobenius = 1) : Nat.card (𝓞 K ⧸ D.primeIdeal) = p := by
  let : D.primeIdeal.IsMaximal := D.maximal
  let : CharP (𝓞 K ⧸ D.primeIdeal) p := D.residue_charP
  let F := 𝓞 K ⧸ D.primeIdeal
  let j : ZMod p →+* F := ZMod.castHom (m := p) dvd_rfl F
  have hsurj : Function.Surjective j := by
    intro x
    have hx : x ^ p = x := by
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [← D.residue_frobenius, hF, one_smul]
    have hbot : x ∈ (⊥ : Subfield F) := (Subfield.mem_bot_iff_pow_eq_self F p).mpr hx
    obtain ⟨n, hn⟩ := (mem_bot_iff_intCast p F).mp hbot
    exact ⟨(n : ZMod p), by simpa only [map_intCast] using hn⟩
  calc
    Nat.card (𝓞 K ⧸ D.primeIdeal) = Nat.card (ZMod p) :=
      (Nat.card_eq_of_bijective j ⟨j.injective, hsurj⟩).symm
    _ = p := by simp

end GeneralFrobenius

/-- The actual Kummer arithmetic Frobenius is identity whenever q divides
the multiplicative index. No splitting assumption is supplied. -/
theorem primeKummer_frobenius_eq_one_of_dvd_index
    {p q : ℕ} {a : ℤ} [Fact p.Prime] [NeZero q] [NeZero a]
    (D : IntegralFrobeniusData (primeKummerField q a) p)
    (ha0 : (a : ZMod p) ≠ 0) (hqi : q ∣ multiplicativeIndex p a) :
    D.frobenius = 1 := by
  let : D.primeIdeal.IsMaximal := D.maximal
  let : CharP (𝓞 (primeKummerField q a) ⧸ D.primeIdeal) p := D.residue_charP
  have hp : p.Prime := Fact.out
  have hqd : q ∣ p - 1 := by
    rw [← orderOf_mul_index hp ha0]
    exact hqi.trans (dvd_mul_left _ _)
  have hpower := (dvd_multiplicativeIndex_iff_isPowerMod hp hqd ha0).mp hqi
  apply primeKummer_aut_eq_one
  · apply (arithFrob_fixes_powerRoot_iff (NeZero.pos q) hqd D.primeIdeal
      D.base_residue_card D.frobenius D.frobenius_spec
      (a := 1) (by simpa using kummerCyclotomicRoot_pow (NeZero.pos q) a)
      (by simp)).mpr
    exact ⟨1, by simp⟩
  · exact (arithFrob_fixes_powerRoot_iff (NeZero.pos q) hqd D.primeIdeal
      D.base_residue_card D.frobenius D.frobenius_spec
      (kummerRadicalRoot_pow (NeZero.pos q) a) ha0).mpr hpower

/-- A fixed Frobenius on the Kummer field forces q to divide p−1,
using the actual primitive root of unity. -/
theorem dvd_pred_of_primeKummer_frobenius_eq_one
    {p q : ℕ} {a : ℤ} [NeZero q] [NeZero a]
    (hp : p.Prime) (D : IntegralFrobeniusData (primeKummerField q a) p)
    (hqp : ¬ (p : ℤ) ∣ (q : ℤ)) (hF : D.frobenius = 1) : q ∣ p - 1 := by
  let ζ : 𝓞 (primeKummerField q a) :=
    ⟨kummerCyclotomicRoot q a,
      powerRoot_isIntegral (NeZero.pos q) (a := 1)
        (by simpa using kummerCyclotomicRoot_pow (NeZero.pos q) a)⟩
  have hζ : ζ ^ q = 1 := by
    apply Subtype.ext
    exact kummerCyclotomicRoot_pow (NeZero.pos q) a
  have hf := D.frobenius_root_of_unity hζ hqp
  rw [hF, one_smul] at hf
  have hζp : primeCyclotomicRoot q ^ p = primeCyclotomicRoot q :=
    (congrArg (fun z : 𝓞 (primeKummerField q a) => ((z : primeKummerField q a) : ℂ)) hf).symm
  have hζ0 : primeCyclotomicRoot q ≠ 0 :=
    (primeCyclotomicRoot_isPrimitiveRoot (NeZero.pos q)).ne_zero (NeZero.ne q)
  have hpow : primeCyclotomicRoot q ^ (p - 1) = 1 := by
    apply mul_right_cancel₀ hζ0
    rw [← pow_succ, Nat.sub_one_add_one hp.ne_zero, hζp, one_mul]
  exact (primeCyclotomicRoot_isPrimitiveRoot (NeZero.pos q)).pow_eq_one_iff_dvd (p - 1) |>.mp hpow

/-- The complete actual Kummer Frobenius/index equivalence away from the
exponent and the radicand. -/
theorem primeKummer_frobenius_eq_one_iff_dvd_index
    {p q : ℕ} {a : ℤ} [Fact p.Prime] [NeZero q] [NeZero a]
    (D : IntegralFrobeniusData (primeKummerField q a) p)
    (hqp : ¬ (p : ℤ) ∣ (q : ℤ)) (ha0 : (a : ZMod p) ≠ 0) :
    D.frobenius = 1 ↔ q ∣ multiplicativeIndex p a := by
  constructor
  · intro hF
    have hqd := dvd_pred_of_primeKummer_frobenius_eq_one (Fact.out : p.Prime) D hqp hF
    let : D.primeIdeal.IsMaximal := D.maximal
    let : CharP (𝓞 (primeKummerField q a) ⧸ D.primeIdeal) p := D.residue_charP
    apply (dvd_multiplicativeIndex_iff_isPowerMod (Fact.out : p.Prime) hqd ha0).mpr
    apply (arithFrob_fixes_powerRoot_iff (NeZero.pos q) hqd D.primeIdeal
      D.base_residue_card D.frobenius D.frobenius_spec
      (kummerRadicalRoot_pow (NeZero.pos q) a) ha0).mp
    rw [hF, AlgEquiv.one_apply]
  · exact primeKummer_frobenius_eq_one_of_dvd_index D ha0

end ArtinMatthews
