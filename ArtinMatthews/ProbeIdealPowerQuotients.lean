module

public import ArtinMatthews.ProbeIdealPrimeUniformizer
public import Mathlib.GroupTheory.Index
public import Mathlib.NumberTheory.NumberField.Ideal.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! Reduction and uniformizer multiplication on actual powers of an
arbitrary height-one prime ideal. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open IsDedekindDomain
open scoped Classical
noncomputable section

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

def probePrimePowerReduction (P : HeightOneSpectrum R) (m n : ℕ) (hnm : n ≤ m) :
    (R ⧸ P.asIdeal ^ m) →+* (R ⧸ P.asIdeal ^ n) :=
  Ideal.Quotient.factor (Ideal.pow_le_pow_right hnm)

omit [IsDedekindDomain R] in
theorem probePrimePowerReduction_mk (P : HeightOneSpectrum R) (m n : ℕ)
    (hnm : n ≤ m) (x : R) :
    probePrimePowerReduction P m n hnm (Ideal.Quotient.mk (P.asIdeal ^ m) x) =
      Ideal.Quotient.mk (P.asIdeal ^ n) x := rfl

omit [IsDedekindDomain R] in
theorem probePrimePowerReduction_surjective (P : HeightOneSpectrum R)
    (m n : ℕ) (hnm : n ≤ m) : Function.Surjective (probePrimePowerReduction P m n hnm) :=
  Ideal.Quotient.factor_surjective _

def probePrimePowerScale (P : HeightOneSpectrum R) (n k : ℕ) :
    (R ⧸ P.asIdeal ^ n) →+ (R ⧸ P.asIdeal ^ (n + k)) :=
  QuotientAddGroup.lift (P.asIdeal ^ n).toAddSubgroup
    { toFun := fun x => Ideal.Quotient.mk (P.asIdeal ^ (n + k)) (probeIdealUniformizer P ^ k * x)
      map_zero' := by simp
      map_add' := by simp [mul_add] }
    (by
      intro x hx
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      exact (probeIdealUniformizer_pow_mul_mem_iff P n k x).mpr hx)

theorem probePrimePowerScale_mk (P : HeightOneSpectrum R) (n k : ℕ) (x : R) :
    probePrimePowerScale P n k (Ideal.Quotient.mk (P.asIdeal ^ n) x) =
      Ideal.Quotient.mk (P.asIdeal ^ (n + k)) (probeIdealUniformizer P ^ k * x) := rfl

theorem probePrimePowerScale_injective (P : HeightOneSpectrum R) (n k : ℕ) :
    Function.Injective (probePrimePowerScale P n k) := by
  apply (probePrimePowerScale P n k).ker_eq_bot_iff.mp
  apply bot_unique
  intro x hx
  change probePrimePowerScale P n k x = 0 at hx
  change x = 0
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [probePrimePowerScale_mk, Ideal.Quotient.eq_zero_iff_mem] at hx
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    ((probeIdealUniformizer_pow_mul_mem_iff P n k x).mp hx)

theorem probePrimePowerScale_mul (P : HeightOneSpectrum R) (n k : ℕ)
    (x : R ⧸ P.asIdeal ^ n) (y : R ⧸ P.asIdeal ^ (n + k)) :
    probePrimePowerScale P n k x * y = probePrimePowerScale P n k
      (x * probePrimePowerReduction P (n + k) n (Nat.le_add_right n k) y) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [probePrimePowerScale_mk, probePrimePowerReduction_mk,
    ← map_mul (Ideal.Quotient.mk (P.asIdeal ^ n)) x y,
    probePrimePowerScale_mk, ← map_mul, mul_assoc]

theorem probePrimePowerScale_range (P : HeightOneSpectrum R) (n k : ℕ) :
    Set.range (probePrimePowerScale P n k) =
      {x | probePrimePowerReduction P (n + k) k (Nat.le_add_left k n) x = 0} := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    change Ideal.Quotient.mk (P.asIdeal ^ k) (probeIdealUniformizer P ^ k * y) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact (P.asIdeal ^ k).mul_mem_right y (probeIdealUniformizer_pow_mem P k)
  · intro hx
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk (P.asIdeal ^ k) x = 0 at hx
    have hmem := Ideal.Quotient.eq_zero_iff_mem.mp hx
    obtain ⟨y, hy⟩ := probeIdealUniformizer_approx P n k x hmem
    refine ⟨Ideal.Quotient.mk (P.asIdeal ^ n) y, ?_⟩
    rw [probePrimePowerScale_mk, Ideal.Quotient.eq]
    simpa only [neg_sub] using (P.asIdeal ^ (n + k)).neg_mem hy

def probePrimePowerLowerChar (P : HeightOneSpectrum R) (n k : ℕ)
    (ψ : AddChar (R ⧸ P.asIdeal ^ (n + k)) ℂ) : AddChar (R ⧸ P.asIdeal ^ n) ℂ :=
  ψ.compAddMonoidHom (probePrimePowerScale P n k)

theorem probePrimePowerLowerChar_mk (P : HeightOneSpectrum R) (n k : ℕ)
    (ψ : AddChar (R ⧸ P.asIdeal ^ (n + k)) ℂ) (x : R) :
    probePrimePowerLowerChar P n k ψ (Ideal.Quotient.mk (P.asIdeal ^ n) x) =
      ψ (Ideal.Quotient.mk (P.asIdeal ^ (n + k)) (probeIdealUniformizer P ^ k * x)) := rfl

theorem probePrimePowerLowerChar_primitive (P : HeightOneSpectrum R) (n k : ℕ)
    (ψ : AddChar (R ⧸ P.asIdeal ^ (n + k)) ℂ) (hψ : ψ.IsPrimitive) :
    (probePrimePowerLowerChar P n k ψ).IsPrimitive := by
  intro x hx he
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hn : Ideal.Quotient.mk (P.asIdeal ^ (n + k)) (probeIdealUniformizer P ^ k * x) ≠ 0 := by
    intro hz
    apply hx
    apply probePrimePowerScale_injective P n k
    simpa only [probePrimePowerScale_mk, map_zero] using hz
  apply hψ hn
  ext y
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  have ht := congrArg (fun φ : AddChar (R ⧸ P.asIdeal ^ n) ℂ =>
    φ (Ideal.Quotient.mk (P.asIdeal ^ n) y)) he
  simpa only [AddChar.mulShift_apply, ← map_mul, probePrimePowerLowerChar_mk,
    mul_assoc, AddChar.one_apply] using ht

open scoped NumberField
variable {K : Type*} [Field K] [NumberField K]

theorem probePrimePowerReduction_kernel_card (P : HeightOneSpectrum (𝓞 K)) (n k : ℕ) :
    Nat.card (probePrimePowerReduction P (n + k) n (Nat.le_add_right n k)).toAddMonoidHom.ker =
      Ideal.absNorm P.asIdeal ^ k := by
  have hc := AddSubgroup.card_ker_mul_card_of_surjective
    (f := (probePrimePowerReduction P (n + k) n (Nat.le_add_right n k)).toAddMonoidHom)
    (probePrimePowerReduction_surjective P (n + k) n (Nat.le_add_right n k))
  have hnorm (m : ℕ) : Nat.card ((𝓞 K) ⧸ P.asIdeal ^ m) = Ideal.absNorm P.asIdeal ^ m := by
    rw [← map_pow, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hp : Ideal.absNorm P.asIdeal ^ (n + k) =
      Ideal.absNorm P.asIdeal ^ n * Ideal.absNorm P.asIdeal ^ k := pow_add _ _ _
  rw [hnorm, hnorm, hp] at hc
  have hpos : 0 < Ideal.absNorm P.asIdeal ^ n := by
    apply pow_pos
    exact Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr P.ne_bot)
  exact Nat.eq_of_mul_eq_mul_right hpos (hc.trans (Nat.mul_comm _ _))

end

end ArtinMatthews.VaryingKummerAnalytic
