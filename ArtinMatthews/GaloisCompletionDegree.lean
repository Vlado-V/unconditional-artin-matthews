module

public import ValuedFieldTheory.Ramification.HilbertRamification.DecompositionFieldLocalization
public import ValuedFieldTheory.Valuation.Completion.FiniteLocalization
public import Mathlib.GroupTheory.Coset.Card


set_option backward.privateInPublic true
@[expose] public section

/-! Local degrees divide the global degree for a finite Galois extension.
The proof identifies the actual completion with the algebraic localization,
whose automorphisms form the actual decomposition subgroup. -/

noncomputable section

namespace ArtinMatthews

open AlgebraicNumberTheory.Valuations HilbertRamification

universe u v

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
variable [FiniteDimensional K L] [IsGalois K L]

theorem galois_absoluteCompletion_finrank_dvd
    (a : AbsoluteValue K ℝ) (ha : a.IsNontrivial)
    (w : AbsoluteValueExtension a L) :
    let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    let : SMul K w.1.Completion := hK.toSMul
    let := AbsoluteValue.completionAlgebra a w.1 w.2
    Module.finrank a.Completion w.1.Completion ∣ Module.finrank K L := by
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let := AbsoluteValue.completionAlgebra a w.1 w.2
  change Module.finrank a.Completion w.1.Completion ∣ Module.finrank K L
  let E := LocalizedCompletion a w
  let : Module.Finite a.Completion E := localizedCompletionModuleFinite a ha w
  let : IsGalois a.Completion E := algebraicLocalization_isGalois a w
  have hc : Nat.card (absoluteValueDecompositionGroup K w.1) =
      Module.finrank a.Completion E := by
    calc
      Nat.card (absoluteValueDecompositionGroup K w.1) =
          Nat.card (E ≃ₐ[a.Completion] E) :=
        Nat.card_congr (decompositionGroupEquivAlgebraicLocalizationAut a ha w).toEquiv
      _ = Module.finrank a.Completion E := IsGalois.card_aut_eq_finrank _ _
  have hd := (absoluteValueDecompositionGroup K w.1).card_subgroup_dvd_card
  rw [hc, IsGalois.card_aut_eq_finrank] at hd
  rw [← (localizedCompletionEquivCompletion a ha w).toLinearEquiv.finrank_eq]
  exact hd

end ArtinMatthews
