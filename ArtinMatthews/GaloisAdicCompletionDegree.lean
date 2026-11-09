module

public import ArtinMatthews.GaloisCompletionDegree
public import ClassFieldTheory.AlgebraicNumberTheory.Completion.AdicCompletionComparison


set_option backward.privateInPublic true
@[expose] public section

/-! Divisibility of the degree of the actual finite-place adic completions.
Both completion comparisons preserve the canonical base embedding. -/

noncomputable section

open scoped NumberField
open NumberField IsDedekindDomain AlgebraicNumberTheory.Valuations

namespace ArtinMatthews

universe u v

variable {K : Type u} {L : Type v} [Field K] [NumberField K]
variable [Field L] [NumberField L] [Algebra K L]
variable [FiniteDimensional K L] [IsGalois K L]

theorem galois_adicCompletion_finrank_dvd
    (v : HeightOneSpectrum (𝓞 K))
    (W : {W : HeightOneSpectrum (𝓞 L) // finitePlaceBelow (K := K) W = v}) :
    let : Algebra (v.adicCompletion K) (W.1.adicCompletion L) :=
      (finitePlaceAdicCompletionMap K L v W).toAlgebra
    Module.finrank (v.adicCompletion K) (W.1.adicCompletion L) ∣
      Module.finrank K L := by
  classical
  obtain ⟨w, rfl⟩ := (finitePlaceExtensionEquivAbove (K := K) (L := L) v).surjective W
  let a := HeightOneSpectrum.adicAbv K v
  let : Algebra (v.adicCompletion K)
      ((finitePlaceExtensionEquivAbove (K := K) (L := L) v w).1.adicCompletion L) :=
    (finitePlaceAdicCompletionMap K L v
      (finitePlaceExtensionEquivAbove (K := K) (L := L) v w)).toAlgebra
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let := AbsoluteValue.completionAlgebra a w.1 w.2
  change Module.finrank (v.adicCompletion K)
    ((finitePlaceExtensionEquivAbove (K := K) (L := L) v w).1.adicCompletion L) ∣
      Module.finrank K L
  have hmap :
      (algebraMap (v.adicCompletion K)
          ((finitePlaceExtensionEquivAbove (K := K) (L := L) v w).1.adicCompletion L)).comp
          (relativeFinitePlaceCompletionAlgEquiv v).toRingHom =
        (finitePlaceExtensionAdicCompletionRingEquiv (K := K) (L := L) v w).toRingHom.comp
          (algebraMap a.Completion w.1.Completion) := by
    apply RingHom.ext
    intro x
    change finitePlaceAdicCompletionMap K L v
        (finitePlaceExtensionEquivAbove (K := K) (L := L) v w)
        ((relativeFinitePlaceCompletionAlgEquiv v) x) =
      (finitePlaceExtensionAdicCompletionRingEquiv (K := K) (L := L) v w)
        (AbsoluteValue.completionMap a w.1 w.2 x)
    rw [← finitePlaceExtensionAdicCompletionMap_eq_finitePlaceAdicCompletionMap]
    change (finitePlaceExtensionAdicCompletionRingEquiv (K := K) (L := L) v w)
        (AbsoluteValue.completionMap a w.1 w.2
          ((relativeFinitePlaceCompletionAlgEquiv v).symm
            ((relativeFinitePlaceCompletionAlgEquiv v) x))) = _
    rw [AlgEquiv.symm_apply_apply]
  have heq := Algebra.finrank_eq_of_equiv_equiv
    (R₀ := a.Completion) (S₀ := w.1.Completion)
    (R₁ := v.adicCompletion K)
    (S₁ := (finitePlaceExtensionEquivAbove (K := K) (L := L) v w).1.adicCompletion L)
    (relativeFinitePlaceCompletionAlgEquiv v).toRingEquiv
    (finitePlaceExtensionAdicCompletionRingEquiv (K := K) (L := L) v w) hmap
  rw [← heq]
  exact galois_absoluteCompletion_finrank_dvd a (RayClass.adicAbv_isNontrivial v) w

theorem galois_adicCompletion_finrank_dvd_six
    (hdeg : Module.finrank K L ∣ 6)
    (v : HeightOneSpectrum (𝓞 K))
    (W : {W : HeightOneSpectrum (𝓞 L) // finitePlaceBelow (K := K) W = v}) :
    let : Algebra (v.adicCompletion K) (W.1.adicCompletion L) :=
      (finitePlaceAdicCompletionMap K L v W).toAlgebra
    Module.finrank (v.adicCompletion K) (W.1.adicCompletion L) ∣ 6 := by
  let : Algebra (v.adicCompletion K) (W.1.adicCompletion L) :=
    (finitePlaceAdicCompletionMap K L v W).toAlgebra
  exact (galois_adicCompletion_finrank_dvd v W).trans hdeg

end ArtinMatthews
