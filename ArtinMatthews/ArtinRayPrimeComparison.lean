module

/-
Copyright (c) 2026 Naganori Yamaguchi. Released under Apache 2.0.
The residue-action proof below is adapted from the pinned ClassFieldTheory
MathlibFrobeniusHilbertComparison theorem (revision 2eb22d6485af45f29c5219de6c49f196a61c4f49).
It retains the actual local-to-global Artin construction and avoids importing
unrelated Hilbert class-field principalization results.
-/
public import ArtinMatthews.ArtinFrobeniusIdealCharacter
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ArithmeticUnramifiedPrimeArtin
public import ClassFieldTheory.AlgebraicNumberTheory.Completion.IntegerRingComparison
public import ClassFieldTheory.AlgebraicNumberTheory.Completion.UnramifiedComparison.IdealToCompletion
public import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.UnramifiedFrobenius


set_option backward.privateInPublic true
@[expose] public section

noncomputable section
open scoped NumberField ValuativeRel Classical
namespace ArtinMatthews.VaryingKummerAnalytic.ArtinRay
open NumberField IsDedekindDomain LocalFieldTheory
open AlgebraicNumberTheory.Valuations
open GaloisIdealCharacter

theorem idealHom_prime_arithmeticArtin
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsAbelianGalois K L]
    (χ : (L ≃ₐ[K] L) →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 K))
    (hunram : Algebra.IsUnramifiedAt (𝓞 K) (primeAbove K L v).val) :
    idealHom K L χ (integralIdealFractionalUnit v.asIdeal v.ne_bot) =
      χ (GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin
        (K := K) (L := L) v) := by
  let w : HeightOneSpectrum (𝓞 L) :=
    ⟨(primeAbove K L v).val, (primeAbove K L v).property.1, primeAbove_ne_bot K L v⟩
  have hw : w.asIdeal.LiesOver v.asIdeal := (primeAbove K L v).property.2
  classical
  let w₀ := chosenFinitePlaceExtension (L := L) v
  let W := finitePlaceExtensionCentre (K := K) (L := L) v w₀
  let P : Ideal (𝓞 K) := v.asIdeal
  let Q : Ideal (𝓞 L) := W.asIdeal
  let G := L ≃ₐ[K] L
  let C := ChosenFinitePlaceBaseCompletion (K := K) v
  let E := ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v
  let : Algebra C E :=
    GlobalClassFieldTheory.Reciprocity.finitePlaceLocalArtinLocalizedAlgebra v w₀
  have hW : Q.LiesOver P :=
    finitePlaceExtensionCentre_liesOver (K := K) (L := L) v w₀
  let : Q.LiesOver P := hW
  let : w.asIdeal.LiesOver P := hw
  let : Finite G := IsGaloisGroup.finite G K L
  let : IsGaloisGroup G (𝓞 K) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing G (𝓞 K) (𝓞 L) K L
  have hEw : w.asIdeal.ramificationIdx (𝓞 K) = 1 :=
    (Ideal.ramificationIdx_eq_one_iff).mpr hunram
  have hEQ : Q.ramificationIdx (𝓞 K) =
      w.asIdeal.ramificationIdx (𝓞 K) :=
    Ideal.ramificationIdx_eq_of_isGaloisGroup P Q w.asIdeal G
  have hunramQ : Algebra.IsUnramifiedAt (𝓞 K) Q :=
    (Ideal.ramificationIdx_eq_one_iff).mp (hEQ.trans hEw)
  have hChosen : ChosenFinitePlaceIsUnramified
      (K := K) (L := L) v :=
    chosenFinitePlaceIsUnramified_of_isUnramifiedAt
      (K := K) (L := L) v hunramQ
  let : IsNonarchimedeanLocalField.IsUnramifiedValuedExtension C E := hChosen
  let vK := HeightOneSpectrum.adicAbv K v
  let eD : HilbertRamification.absoluteValueDecompositionGroup K w₀.1 ≃*
      (E ≃ₐ[C] E) :=
    HilbertRamification.decompositionGroupEquivAlgebraicLocalizationAut
      vK (RayClass.adicAbv_isNontrivial v) w₀
  let f : E ≃ₐ[C] E := arithmeticFrobeniusOfUnramifiedValuation C E
  let δ : HilbertRamification.absoluteValueDecompositionGroup K w₀.1 :=
    eD.symm f
  have heDδ : eD δ = f := eD.apply_symm_apply f
  have hδ : (δ : G) =
      GlobalClassFieldTheory.GlobalClassFields.chosenFinitePlaceArithmeticFrobenius
        (K := K) (L := L) v hChosen := by
    change (eD.symm f : G) =
      GlobalClassFieldTheory.Reciprocity.finitePlaceLocalToGlobalMonoidHom
        (K := K) (L := L) v w₀ f
    rfl
  let e : (𝓞 L ⧸ Q) ≃+* 𝓀[E] :=
    chosenFinitePlaceLocalizedResidueEquiv (K := K) (L := L) v
  have hCard : Nat.card 𝓀[C] =
      Nat.card (𝓞 K ⧸ Q.under (𝓞 K)) := by
    rw [finitePlaceCompletion_residueField_card (K := K) v,
      hW.over.symm]
  have hResidue (x : 𝓞 L) :
      Ideal.Quotient.mk Q
          (NumberField.RingOfIntegers.mapAlgEquiv (δ : G) x) =
        (Ideal.Quotient.mk Q x) ^
          Nat.card (𝓞 K ⧸ Q.under (𝓞 K)) := by
    apply e.injective
    calc
      e (Ideal.Quotient.mk Q
          (NumberField.RingOfIntegers.mapAlgEquiv (δ : G) x)) =
          LocalFieldTheory.galoisGroupResidueAlgEquivOfIsIntegralClosure C E
            (eD δ) (e (Ideal.Quotient.mk Q x)) :=
        chosenFinitePlaceLocalizedResidueEquiv_equivariant
          (K := K) (L := L) v δ x
      _ = LocalFieldTheory.galoisGroupResidueAlgEquivOfIsIntegralClosure C E
            f (e (Ideal.Quotient.mk Q x)) := by
        simp only [heDδ]
      _ = (e (Ideal.Quotient.mk Q x)) ^ Nat.card 𝓀[C] :=
        galoisGroupResidueAlgEquivOfIsIntegralClosure_arithmeticFrobenius_apply
          C E (e (Ideal.Quotient.mk Q x))
      _ = e ((Ideal.Quotient.mk Q x) ^
            Nat.card (𝓞 K ⧸ Q.under (𝓞 K))) := by
        exact (congrArg
          (fun n : ℕ => (e (Ideal.Quotient.mk Q x)) ^ n) hCard).trans
          (map_pow e (Ideal.Quotient.mk Q x) _).symm
  have hArith : IsArithFrobAt (𝓞 K) (δ : G) Q := by
    intro x
    change NumberField.RingOfIntegers.mapAlgEquiv (δ : G) x -
        x ^ Nat.card (𝓞 K ⧸ Q.under (𝓞 K)) ∈ Q
    rw [← Ideal.Quotient.eq, map_pow]
    exact hResidue x
  let : Algebra.IsUnramifiedAt (𝓞 K) Q := hunramQ
  calc
    idealHom K L χ (integralIdealFractionalUnit v.asIdeal v.ne_bot) = χ (δ : G) :=
      idealHom_prime_frobenius K L χ v Q hW.over.symm (δ : G) hArith
    _ = χ (GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin
        (K := K) (L := L) v) := by
      rw [hδ, GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin_eq_chosenFinitePlaceArithmeticFrobenius
        (K := K) (L := L) v hChosen]

end ArtinMatthews.VaryingKummerAnalytic.ArtinRay
end
