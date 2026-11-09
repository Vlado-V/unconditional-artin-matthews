module

public import ArtinMatthews.SourceRowTwistExceptional


set_option backward.privateInPublic true
@[expose] public section

/-! Transfer the genuine primitive zero-density and reciprocal bounds to
literal source rows. This uses actual old conductors and keeps the fixed
Euler deletions when passing to the reciprocal. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic
open OAI.SevenEighths.FiniteFourier
open scoped NumberField Classical BigOperators nonZeroDivisors
noncomputable section
variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
variable {M : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F M) (hM : M ≠ ⊥)
local notation "R" => sourceRing F S₀
local notation "S" => sourceHilbertSet F S₀

omit [IsTotallyComplex F] in
include hζ in
theorem sourceRowTwistFamilyOldModulus_norm_le_of_frequencyBound
    {ι : Type} (f : ι → {u : R // u ≠ 0}) (Q : ℕ)
    (hQ : ∀ i, sourcePrimeExponentNorm F S₀ (sourceElementExponents F S₀
      (f i).val (f i).property) ≤ Q) :
    ∀ i, (sourceRowTwistFamilyOldModulus F S₀ (M := M) f i).absNorm ≤
      M.absNorm * (sixthKummerFixedIdeal S).absNorm * Q := by
  intro i
  exact (sourceRowTwistFamilyOldModulus_norm_le F hζ S₀ (M := M) f i).trans
    (Nat.mul_le_mul_left _ (hQ i))

theorem sourceRowTwistReciprocal_eq_family_old {ι : Type} (f : ι → {u : R // u ≠ 0})
    (i : SourceNonprincipalTwistRow F hζ S₀ η hM f) (s : ℂ) :
    sourceRowTwistReciprocal F hζ S₀ (f i.val).val (f i.val).property η hM s =
      ((sourceRowTwistFamilyCharacter F hζ S₀ η hM f i).idealCoprimeContinued
        (sourceRowTwistFamilyModulus F hζ S₀ η hM f i).property
        (sourceRowTwistFamilyCharacter_primitive F hζ S₀ η hM f i)
        (sourceRowTwistFamilyOldModulus F S₀ (M := M) f i.val) s)⁻¹ := by
  unfold sourceRowTwistReciprocal
  rw [sourceRayReciprocalContinued_of_nonprincipal _ _ _ i.property]
  rfl

theorem exists_sourceRowTwist_good_family :
    ∃ r C U₀ : ℝ, 0 < r ∧ r < 1/10 ∧ 0 < C ∧ 2 ≤ U₀ ∧
      (∀ {ι : Type} [Fintype ι] (f : ι → {u : R // u ≠ 0}) (U : ℝ), U₀ ≤ U →
        (∀ i, ((sourceRowTwistFamilyOldModulus F S₀ (M := M) f i).absNorm : ℝ) ≤ U) →
        (∀ i j, (∃ a : F, a ^ 6 = ((f i).val : F) / ((f j).val : F)) → i = j) →
        ((sourceRowTwistExceptionalRows F hζ S₀ η hM f U r).card : ℝ) ≤ C*U^(1/2 : ℝ)) ∧
      (∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 < B ∧
        ∀ {ι : Type} [Fintype ι] (f : ι → {u : R // u ≠ 0}) (U : ℝ), U₀ ≤ U →
        (∀ i, ((sourceRowTwistFamilyOldModulus F S₀ (M := M) f i).absNorm : ℝ) ≤ U) →
        ∀ i : SourceNonprincipalTwistRow F hζ S₀ η hM f,
          i ∉ sourceRowTwistExceptionalRows F hζ S₀ η hM f U r →
          ∀ s : ℂ, (499/500 : ℝ) ≤ s.re → |s.im| ≤ 2*U^r →
            ‖sourceRowTwistReciprocal F hζ S₀ (f i.val).val (f i.val).property η hM s‖ ≤ B*U^ε) := by
  obtain ⟨r, C, U₀, hr, hr', hC, hU₀, hcount, hgood⟩ :=
    exists_actual_primitive_good_family_with_deletions F
  refine ⟨r, C, U₀, hr, hr', hC, hU₀, ?_, ?_⟩
  · intro ι inst f U hU hn hf
    have H := hcount U hU
      (sourceRowTwistConductorSupport F hζ S₀ η hM f)
      (sourceRowTwistCharactersAt F hζ S₀ η hM f)
      (sourceRowTwistConductorSupport_norm_le F hζ S₀ η hM f U hn)
      (fun N _ ψ hψ => sourceRowTwistCharactersAt_primitive F hζ S₀ η hM f N ψ hψ)
      (fun N _ ψ hψ => sourceRowTwistCharactersAt_nonprincipal F hζ S₀ η hM f N ψ hψ)
    exact (sourceRowTwistExceptionalRows_count F hζ S₀ η hM f U r hf).symm.trans_le H
  · intro ε hε
    obtain ⟨B, hB, hrec⟩ := hgood ε hε
    refine ⟨B, hB, ?_⟩
    intro ι inst f U hU hn i hi s hs him
    rw [sourceRowTwistReciprocal_eq_family_old F hζ S₀ η hM f i s]
    exact hrec U hU
      (sourceRowTwistConductorSupport F hζ S₀ η hM f)
      (sourceRowTwistCharactersAt F hζ S₀ η hM f)
      (sourceRowTwistConductorSupport_norm_le F hζ S₀ η hM f U hn)
      (fun N _ ψ hψ => sourceRowTwistCharactersAt_primitive F hζ S₀ η hM f N ψ hψ)
      (fun N _ ψ hψ => sourceRowTwistCharactersAt_nonprincipal F hζ S₀ η hM f N ψ hψ)
      (sourceRowTwistFamilyModulus F hζ S₀ η hM f i)
      (sourceRowTwistFamilyModulus_mem F hζ S₀ η hM f i)
      (sourceRowTwistFamilyCharacter F hζ S₀ η hM f i)
      (sourceRowTwistFamilyCharacter_mem F hζ S₀ η hM f i)
      (sourceRowTwistFamilyCharacter_primitive F hζ S₀ η hM f i)
      (sourceRowTwistExceptionalRows_complement_coeff F hζ S₀ η hM f U r i hi)
      (sourceRowTwistFamilyOldModulus F S₀ (M := M) f i.val)
      (sourceRowTwistFamilyOldModulus_ne_bot F S₀ hM f i.val) (hn i.val) s hs him

end
end ArtinMatthews.SourceEulerAssembly
