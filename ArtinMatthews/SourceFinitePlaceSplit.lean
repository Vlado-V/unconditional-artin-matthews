module

public import ArtinMatthews.SourceAdelicIntegralHaarProduct
public import ArtinMatthews.SourceKPExteriorUpperCompatibility


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews

open NumberField IsDedekindDomain
open scoped NumberField AdeleRing RestrictedProduct
noncomputable section

variable (K : Type) [Field K] [NumberField K]

theorem sourceKPFiniteAdditiveSingle_same (P : HeightOneSpectrum (𝓞 K))
    (x : P.adicCompletion K) : sourceKPFiniteAdditiveSingle K P x P = x := by
  classical
  exact RestrictedProduct.single_eq_same _ P x

theorem sourceKPFiniteAdditiveSingle_other (P : HeightOneSpectrum (𝓞 K))
    (x : P.adicCompletion K) (Q : HeightOneSpectrum (𝓞 K)) (hQ : Q ≠ P) :
    sourceKPFiniteAdditiveSingle K P x Q = 0 := by
  classical
  exact RestrictedProduct.single_eq_of_ne _ x hQ

theorem sourceKPFiniteAdditiveSingle_add (P : HeightOneSpectrum (𝓞 K))
    (x y : P.adicCompletion K) :
    sourceKPFiniteAdditiveSingle K P (x + y) =
      sourceKPFiniteAdditiveSingle K P x + sourceKPFiniteAdditiveSingle K P y := by
  classical
  exact RestrictedProduct.single_add _ P x y

theorem sourceKPFiniteAdditiveSingle_continuous (P : HeightOneSpectrum (𝓞 K)) :
    Continuous (sourceKPFiniteAdditiveSingle K P) := by
  classical
  let S : Set (HeightOneSpectrum (𝓞 K)) := {Q | Q ≠ P}
  have hS : Filter.cofinite ≤ Filter.principal S :=
    Filter.le_principal_iff.mpr (Filter.eventually_cofinite_ne P)
  let f : P.adicCompletion K →
      Πʳ Q : HeightOneSpectrum (𝓞 K),
        [Q.adicCompletion K, Q.adicCompletionIntegers K]_[Filter.principal S] := fun x =>
    ⟨sourceKPFiniteAdditiveSingle K P x, by
      change ∀ Q ∈ S, sourceKPFiniteAdditiveSingle K P x Q ∈ Q.adicCompletionIntegers K
      intro Q hQ
      rw [sourceKPFiniteAdditiveSingle_other K P x Q hQ]
      exact zero_mem _⟩
  have hf : Continuous f := by
    apply RestrictedProduct.continuous_rng_of_principal_iff_forall.mpr
    intro Q
    change Continuous (fun x : P.adicCompletion K => sourceKPFiniteAdditiveSingle K P x Q)
    by_cases hQ : Q = P
    · subst Q
      exact (continuous_id : Continuous (fun x : P.adicCompletion K => x)).congr
        (fun x => (sourceKPFiniteAdditiveSingle_same K P x).symm)
    · exact (continuous_const : Continuous (fun _ : P.adicCompletion K =>
        (0 : Q.adicCompletion K))).congr
        (fun x => (sourceKPFiniteAdditiveSingle_other K P x Q hQ).symm)
  exact (RestrictedProduct.continuous_inclusion hS).comp hf

def sourceKPFinitePlaceRemainder (P : HeightOneSpectrum (𝓞 K)) : AddSubgroup 𝔸ᶠ[K] :=
  (RestrictedProduct.evalAddMonoidHom
    (fun Q : HeightOneSpectrum (𝓞 K) => Q.adicCompletion K) P).ker

theorem sourceKPFinitePlaceRemainder_mem (P : HeightOneSpectrum (𝓞 K)) (x : 𝔸ᶠ[K]) :
    x ∈ sourceKPFinitePlaceRemainder K P ↔ x P = 0 := Iff.rfl

def sourceKPFinitePlaceSeparate (P : HeightOneSpectrum (𝓞 K)) (x : 𝔸ᶠ[K]) :
    P.adicCompletion K × sourceKPFinitePlaceRemainder K P :=
  (x P, ⟨x - sourceKPFiniteAdditiveSingle K P (x P), by
    change x P - sourceKPFiniteAdditiveSingle K P (x P) P = 0
    rw [sourceKPFiniteAdditiveSingle_same, sub_self]⟩)

def sourceKPFinitePlaceMerge (P : HeightOneSpectrum (𝓞 K))
    (p : P.adicCompletion K × sourceKPFinitePlaceRemainder K P) : 𝔸ᶠ[K] :=
  sourceKPFiniteAdditiveSingle K P p.1 + p.2.val

def sourceKPFinitePlaceSplitAddEquiv (P : HeightOneSpectrum (𝓞 K)) :
    𝔸ᶠ[K] ≃+ (P.adicCompletion K × sourceKPFinitePlaceRemainder K P) where
  toFun := sourceKPFinitePlaceSeparate K P
  invFun := sourceKPFinitePlaceMerge K P
  left_inv x := by
    change sourceKPFiniteAdditiveSingle K P (x P) +
      (x - sourceKPFiniteAdditiveSingle K P (x P)) = x
    abel
  right_inv p := by
    have hp : p.2.val P = 0 := p.2.property
    apply Prod.ext
    · change sourceKPFiniteAdditiveSingle K P p.1 P + p.2.val P = p.1
      rw [sourceKPFiniteAdditiveSingle_same, hp, add_zero]
    · apply Subtype.ext
      change sourceKPFiniteAdditiveSingle K P p.1 + p.2.val -
        sourceKPFiniteAdditiveSingle K P
          (sourceKPFiniteAdditiveSingle K P p.1 P + p.2.val P) = p.2.val
      rw [sourceKPFiniteAdditiveSingle_same, hp, add_zero]
      abel
  map_add' x y := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      change x + y - sourceKPFiniteAdditiveSingle K P (x P + y P) =
        (x - sourceKPFiniteAdditiveSingle K P (x P)) +
          (y - sourceKPFiniteAdditiveSingle K P (y P))
      rw [sourceKPFiniteAdditiveSingle_add]
      abel

theorem sourceKPFinitePlaceSeparate_continuous (P : HeightOneSpectrum (𝓞 K)) :
    Continuous (sourceKPFinitePlaceSeparate K P) := by
  exact (RestrictedProduct.continuous_eval P).prodMk
    ((continuous_id.sub
      ((sourceKPFiniteAdditiveSingle_continuous K P).comp
        (RestrictedProduct.continuous_eval P))).subtype_mk _)

theorem sourceKPFinitePlaceMerge_continuous (P : HeightOneSpectrum (𝓞 K)) :
    Continuous (sourceKPFinitePlaceMerge K P) :=
  ((sourceKPFiniteAdditiveSingle_continuous K P).comp continuous_fst).add
    (continuous_subtype_val.comp continuous_snd)

def sourceKPFinitePlaceSplit (P : HeightOneSpectrum (𝓞 K)) :
    𝔸ᶠ[K] ≃ₜ+ (P.adicCompletion K × sourceKPFinitePlaceRemainder K P) where
  toAddEquiv := sourceKPFinitePlaceSplitAddEquiv K P
  continuous_toFun := sourceKPFinitePlaceSeparate_continuous K P
  continuous_invFun := sourceKPFinitePlaceMerge_continuous K P

theorem sourceKPFinitePlaceSplit_symm_apply (P : HeightOneSpectrum (𝓞 K))
    (x : P.adicCompletion K) (y : sourceKPFinitePlaceRemainder K P) :
    (sourceKPFinitePlaceSplit K P).symm (x, y) =
      sourceKPFiniteAdditiveSingle K P x + y.val := rfl

theorem sourceKPFinitePlaceSplit_fst (P : HeightOneSpectrum (𝓞 K)) (x : 𝔸ᶠ[K]) :
    (sourceKPFinitePlaceSplit K P x).1 = x P := rfl

theorem sourceKPFinitePlaceRemainder_isClosed (P : HeightOneSpectrum (𝓞 K)) :
    IsClosed (sourceKPFinitePlaceRemainder K P : Set 𝔸ᶠ[K]) :=
  isClosed_eq (RestrictedProduct.continuous_eval P) continuous_const

end
end ArtinMatthews
