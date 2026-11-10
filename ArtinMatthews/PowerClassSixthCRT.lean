module

public import ArtinMatthews.SLocalWeakApproximation
public import ArtinMatthews.SLocalPowerModule
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
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
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

/-! Exact sixth-power CRT for actual local power classes. The maps send
the class of a to its classes modulo squares and cubes; surjectivity
uses the literal lift a^3*b^4. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain ClassFieldTheory
open scoped NumberField Classical
noncomputable section

variable (G : Type*) [CommGroup G]

def powerQuotientMapOfDvd (n m : ℕ) (hmn : m ∣ n) :
    (G ⧸ (powMonoidHom n : G →* G).range) →*
      (G ⧸ (powMonoidHom m : G →* G).range) :=
  QuotientGroup.map _ _ (MonoidHom.id G) (by
    rintro _ ⟨a, rfl⟩
    obtain ⟨k, hk⟩ := hmn
    refine ⟨a ^ k, ?_⟩
    change (a ^ k) ^ m = a ^ n
    rw [← pow_mul, Nat.mul_comm k m, ← hk])

@[simp] theorem powerQuotientMapOfDvd_mk (n m : ℕ) (hmn : m ∣ n) (a : G) :
    powerQuotientMapOfDvd G n m hmn (QuotientGroup.mk' _ a) = QuotientGroup.mk' _ a := rfl

def powerQuotientSixthCRTMap :
    (G ⧸ (powMonoidHom 6 : G →* G).range) →*
      ((G ⧸ (powMonoidHom 2 : G →* G).range) ×
        (G ⧸ (powMonoidHom 3 : G →* G).range)) :=
  (powerQuotientMapOfDvd G 6 2 (by decide)).prod
    (powerQuotientMapOfDvd G 6 3 (by decide))

@[simp] theorem powerQuotientSixthCRTMap_mk (a : G) :
    powerQuotientSixthCRTMap G (QuotientGroup.mk' _ a) =
      (QuotientGroup.mk' _ a, QuotientGroup.mk' _ a) := rfl

theorem powerQuotientSixthCRTMap_injective : Function.Injective (powerQuotientSixthCRTMap G) := by
  apply (powerQuotientSixthCRTMap G).ker_eq_bot_iff.mp
  apply le_antisymm _ bot_le
  intro q hq
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective _ q
  change (QuotientGroup.mk' (powMonoidHom 2 : G →* G).range a,
    QuotientGroup.mk' (powMonoidHom 3 : G →* G).range a) = (1, 1) at hq
  obtain ⟨b, hb⟩ := (QuotientGroup.eq_one_iff _).mp (congrArg Prod.fst hq)
  obtain ⟨c, hc⟩ := (QuotientGroup.eq_one_iff _).mp (congrArg Prod.snd hq)
  change b ^ 2 = a at hb
  change c ^ 3 = a at hc
  change QuotientGroup.mk' _ a = 1
  apply (QuotientGroup.eq_one_iff _).mpr
  refine ⟨b / c, ?_⟩
  change (b / c) ^ 6 = a
  calc
    (b / c) ^ 6 = (b ^ 2) ^ 3 / (c ^ 3) ^ 2 := by rw [div_pow, ← pow_mul, ← pow_mul]
    _ = a ^ 3 / a ^ 2 := by rw [hb, hc]
    _ = a := by rw [show 3 = 2 + 1 by decide, pow_succ, mul_div_cancel_left]

theorem powerQuotientSixthCRTMap_surjective : Function.Surjective (powerQuotientSixthCRTMap G) := by
  rintro ⟨q, r⟩
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective _ q
  obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective _ r
  let f := QuotientGroup.mk' (powMonoidHom 2 : G →* G).range
  let g := QuotientGroup.mk' (powMonoidHom 3 : G →* G).range
  have ha₂ : f a ^ 2 = 1 := powerQuotient_pow_eq_one 2 _
  have hb₂ : f b ^ 2 = 1 := powerQuotient_pow_eq_one 2 _
  have ha₃ : g a ^ 3 = 1 := powerQuotient_pow_eq_one 3 _
  have hb₃ : g b ^ 3 = 1 := powerQuotient_pow_eq_one 3 _
  have ha₂' : f a ^ 3 = f a := by rw [show 3 = 2 + 1 by decide, pow_succ, ha₂, one_mul]
  have hb₂' : f b ^ 4 = 1 := by rw [show 4 = 2 * 2 by decide, pow_mul, hb₂, one_pow]
  have hb₃' : g b ^ 4 = g b := by rw [show 4 = 3 + 1 by decide, pow_succ, hb₃, one_mul]
  refine ⟨QuotientGroup.mk' _ (a ^ 3 * b ^ 4), ?_⟩
  change (f (a ^ 3 * b ^ 4), g (a ^ 3 * b ^ 4)) = (f a, g b)
  apply Prod.ext
  · change f (a ^ 3 * b ^ 4) = f a
    rw [map_mul, map_pow, map_pow, ha₂', hb₂', mul_one]
  · change g (a ^ 3 * b ^ 4) = g b
    rw [map_mul, map_pow, map_pow, ha₃, hb₃', one_mul]

def powerQuotientSixthCRT :
    (G ⧸ (powMonoidHom 6 : G →* G).range) ≃*
      ((G ⧸ (powMonoidHom 2 : G →* G).range) ×
        (G ⧸ (powMonoidHom 3 : G →* G).range)) :=
  MulEquiv.ofBijective (powerQuotientSixthCRTMap G)
    ⟨powerQuotientSixthCRTMap_injective G, powerQuotientSixthCRTMap_surjective G⟩

@[simp] theorem powerQuotientSixthCRT_mk (a : G) :
    powerQuotientSixthCRT G (QuotientGroup.mk' _ a) =
      (QuotientGroup.mk' _ a, QuotientGroup.mk' _ a) := rfl

variable (F : Type*) [Field F]

def fieldPowerClassSixthCRT : PowerClassGroup F 6 ≃* (PowerClassGroup F 2 × PowerClassGroup F 3) := by
  unfold PowerClassGroup
  exact powerQuotientSixthCRT Fˣ

@[simp] theorem fieldPowerClassSixthCRT_powerClass (a : Fˣ) :
    fieldPowerClassSixthCRT F (powerClass F 6 a) = (powerClass F 2 a, powerClass F 3 a) := rfl

variable (K : Type) [Field K] [NumberField K]

def sLocalSixthCRT (S : Finset (HeightOneSpectrum (𝓞 K))) :
    SLocalPowerClasses K 6 S ≃* (SLocalPowerClasses K 2 S × SLocalPowerClasses K 3 S) where
  toFun x := (fun v => (fieldPowerClassSixthCRT (v.1.adicCompletion K) (x v)).1,
    fun v => (fieldPowerClassSixthCRT (v.1.adicCompletion K) (x v)).2)
  invFun x v := (fieldPowerClassSixthCRT (v.1.adicCompletion K)).symm (x.1 v, x.2 v)
  left_inv x := by funext v; exact (fieldPowerClassSixthCRT (v.1.adicCompletion K)).symm_apply_apply (x v)
  right_inv x := by
    apply Prod.ext
    · funext v
      exact congrArg Prod.fst ((fieldPowerClassSixthCRT (v.1.adicCompletion K)).apply_symm_apply _)
    · funext v
      exact congrArg Prod.snd ((fieldPowerClassSixthCRT (v.1.adicCompletion K)).apply_symm_apply _)
  map_mul' x y := by
    apply Prod.ext
    · funext v
      exact congrArg Prod.fst (map_mul (fieldPowerClassSixthCRT (v.1.adicCompletion K)) (x v) (y v))
    · funext v
      exact congrArg Prod.snd (map_mul (fieldPowerClassSixthCRT (v.1.adicCompletion K)) (x v) (y v))

@[simp] theorem sLocalSixthCRT_globalClass (S : Finset (HeightOneSpectrum (𝓞 K))) (a : Kˣ) :
    sLocalSixthCRT K S (sLocalGlobalClassMap K 6 S a) =
      (sLocalGlobalClassMap K 2 S a, sLocalGlobalClassMap K 3 S a) := by
  apply Prod.ext <;> funext v <;> rfl

@[simp] theorem sLocalSixthCRT_unitClass (S : Finset (HeightOneSpectrum (𝓞 K)))
    (a : SUnitGroup (K := K) S) :
    sLocalSixthCRT K S (sLocalUnitClassMap K 6 S a) =
      (sLocalUnitClassMap K 2 S a, sLocalUnitClassMap K 3 S a) := by
  apply Prod.ext <;> funext v <;> rfl

end
end ArtinMatthews
