module

public import ArtinMatthews.CubicReciprocityBridgeIntegral
public import Mathlib.FieldTheory.Finite.Basic


set_option backward.privateInPublic true
@[expose] public section

/-!+# Rational Frobenius as an Eisenstein Frobenius

At a rational prime congruent to one modulo three, the actual rational
Frobenius fixes the Eisenstein base. Its base residue field consequently has
exactly `p` elements, so the same lift is an arithmetic Frobenius for the
oriented integral Eisenstein extension.
-/

noncomputable section
open scoped NumberField

namespace ArtinMatthews
open OAI.SevenEighths.HeckeFamily

local notation "EO" => OAI.SevenEighths.HeckeFamily.O

namespace IntegralFrobeniusData

attribute [local instance] Ideal.Quotient.field

variable {S : Finset ℤ} {p : ℕ} [Fact p.Prime]
  (D : IntegralFrobeniusData (integerCubicField S) p)

/-- The prime below the chosen rational Frobenius prime in the actual
oriented Eisenstein base. -/
def eisensteinPrime : Ideal EO := D.primeIdeal.under EO

omit [Fact p.Prime] in
theorem eisensteinPrime_maximal : D.eisensteinPrime.IsMaximal := by
  have : D.primeIdeal.IsMaximal := D.maximal
  exact Ideal.isMaximal_under_of_isIntegral_of_isMaximal D.primeIdeal

theorem frobenius_fixes_eisensteinIntegers (hp3 : p % 3 = 1) (a : EO) :
    D.frobenius • heckeKummerIntegersEmbedding S a = heckeKummerIntegersEmbedding S a := by
  exact integerCubicGalois_fixes_heckeIntegers S (relativeCubicFrobenius D hp3) a

/-- The Eisenstein residue field has degree one over the rational prime
field, proved directly from the fixed Frobenius action. -/
theorem eisenstein_residue_card (hp3 : p % 3 = 1) :
    Nat.card (EO ⧸ D.eisensteinPrime) = p := by
  have : D.primeIdeal.IsMaximal := D.maximal
  have : D.eisensteinPrime.IsMaximal := D.eisensteinPrime_maximal
  have : D.primeIdeal.LiesOver D.eisensteinPrime := Ideal.over_under _
  have : CharP (𝓞 (integerCubicField S) ⧸ D.primeIdeal) p := D.residue_charP
  let F := 𝓞 (integerCubicField S) ⧸ D.primeIdeal
  let j : (EO ⧸ D.eisensteinPrime) →+* F := algebraMap _ _
  have hj (x : EO ⧸ D.eisensteinPrime) : (j x) ^ p = j x := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    change (Ideal.Quotient.mk D.primeIdeal (heckeKummerIntegersEmbedding S a)) ^ p =
      Ideal.Quotient.mk D.primeIdeal (heckeKummerIntegersEmbedding S a)
    rw [← D.residue_frobenius, D.frobenius_fixes_eisensteinIntegers hp3]
  let j₀ : (EO ⧸ D.eisensteinPrime) →+* (⊥ : Subfield F) :=
    j.codRestrict (⊥ : Subfield F).toSubring (fun x =>
      (Subfield.mem_bot_iff_pow_eq_self F p).mpr (hj x))
  have hinj : Function.Injective j₀ := by
    intro x y h
    exact j.injective (congrArg (fun z : (⊥ : Subfield F) => (z : F)) h)
  have hsurj : Function.Surjective j₀ := by
    intro x
    obtain ⟨n, hn⟩ := (mem_bot_iff_intCast p F).mp x.property
    refine ⟨(n : EO ⧸ D.eisensteinPrime), ?_⟩
    apply Subtype.ext
    change j (n : EO ⧸ D.eisensteinPrime) = (x : F)
    simpa only [map_intCast] using hn
  calc
    Nat.card (EO ⧸ D.eisensteinPrime) = Nat.card (⊥ : Subfield F) :=
      Nat.card_eq_of_bijective j₀ ⟨hinj, hsurj⟩
    _ = p := Subfield.card_bot F p

/-- The rational Frobenius is literally an arithmetic Frobenius over the
Eisenstein base, since its residue cardinality is the same prime `p`. -/
theorem relative_isArithFrobAt (hp3 : p % 3 = 1) :
    IsArithFrobAt EO (relativeCubicFrobenius D hp3) D.primeIdeal := by
  intro x
  change (relativeCubicFrobenius D hp3) • x -
    x ^ Nat.card (EO ⧸ D.eisensteinPrime) ∈ D.primeIdeal
  rw [D.eisenstein_residue_card hp3]
  exact D.frobenius_sub_pow_mem x

/-- The same prime and the same Frobenius lift, now bundled over the
oriented Eisenstein base. -/
def toEisensteinFrobeniusData (hp3 : p % 3 = 1) :
    EisensteinFrobeniusData S D.eisensteinPrime where
  primeIdeal := D.primeIdeal
  maximal := D.maximal
  liesOver := Ideal.over_under _
  frobenius := relativeCubicFrobenius D hp3
  frobenius_spec := D.relative_isArithFrobAt hp3

@[simp] theorem toEisensteinFrobeniusData_frobenius (hp3 : p % 3 = 1) :
    (D.toEisensteinFrobeniusData hp3).frobenius = relativeCubicFrobenius D hp3 := rfl

@[simp] theorem toEisensteinFrobeniusData_primeIdeal (hp3 : p % 3 = 1) :
    (D.toEisensteinFrobeniusData hp3).primeIdeal = D.primeIdeal := rfl

end IntegralFrobeniusData
end ArtinMatthews
