module

public import ArtinMatthews.SourceFinitePlaceSplit
public import ArtinMatthews.SourceFiniteWindowExhaustion


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews

open NumberField IsDedekindDomain
open scoped NumberField AdeleRing Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K]

theorem sourceKPFiniteWindow_single_add (S : Finset (HeightOneSpectrum (𝓞 K)))
    (P : HeightOneSpectrum (𝓞 K)) (x : P.adicCompletion K)
    (r : sourceKPFinitePlaceRemainder K P) :
    sourceKPFiniteAdditiveSingle K P x + r.val ∈ sourceKPFiniteWindow K S ↔
      (P ∉ S → x ∈ P.adicCompletionIntegers K) ∧ r.val ∈ sourceKPFiniteWindow K S := by
  classical
  have hr0 : r.val P = 0 := r.property
  constructor
  · intro h
    constructor
    · intro hP
      have hx := h P hP
      change sourceKPFiniteAdditiveSingle K P x P + r.val P ∈ P.adicCompletionIntegers K at hx
      rwa [sourceKPFiniteAdditiveSingle_same, hr0, add_zero] at hx
    · intro Q hQ
      by_cases hQP : Q = P
      · subst Q
        rw [hr0]
        exact zero_mem _
      · have hx := h Q hQ
        change sourceKPFiniteAdditiveSingle K P x Q + r.val Q ∈ Q.adicCompletionIntegers K at hx
        rwa [sourceKPFiniteAdditiveSingle_other K P x Q hQP, zero_add] at hx
  · rintro ⟨hx, hr⟩ Q hQ
    change sourceKPFiniteAdditiveSingle K P x Q + r.val Q ∈ Q.adicCompletionIntegers K
    by_cases hQP : Q = P
    · subst Q
      rw [sourceKPFiniteAdditiveSingle_same, hr0, add_zero]
      exact hx hQ
    · rw [sourceKPFiniteAdditiveSingle_other K P x Q hQP, zero_add]
      exact hr Q hQ

theorem sourceKPFiniteWindow_remainder_erase (S : Finset (HeightOneSpectrum (𝓞 K)))
    (P : HeightOneSpectrum (𝓞 K)) (r : sourceKPFinitePlaceRemainder K P) :
    r.val ∈ sourceKPFiniteWindow K (S.erase P) ↔ r.val ∈ sourceKPFiniteWindow K S := by
  classical
  constructor
  · intro h
    exact sourceKPFiniteWindow_mono K (Finset.erase_subset P S) h
  · intro hr Q hQ
    by_cases hQP : Q = P
    · subst Q
      have hr0 : r.val P = 0 := r.property
      rw [hr0]
      exact zero_mem _
    · exact hr Q (fun hQS => hQ (Finset.mem_erase.mpr ⟨hQP, hQS⟩))

theorem sourceKPFiniteWindow_single_add_of_mem (S : Finset (HeightOneSpectrum (𝓞 K)))
    (P : HeightOneSpectrum (𝓞 K)) (hP : P ∈ S) (x : P.adicCompletion K)
    (r : sourceKPFinitePlaceRemainder K P) :
    sourceKPFiniteAdditiveSingle K P x + r.val ∈ sourceKPFiniteWindow K S ↔
      r.val ∈ sourceKPFiniteWindow K S := by
  rw [sourceKPFiniteWindow_single_add]
  simp only [hP, not_true_eq_false, false_implies, true_and]

theorem sourceKPFiniteWindow_single_add_erase (S : Finset (HeightOneSpectrum (𝓞 K)))
    (P : HeightOneSpectrum (𝓞 K)) (x : P.adicCompletion K)
    (r : sourceKPFinitePlaceRemainder K P) :
    sourceKPFiniteAdditiveSingle K P x + r.val ∈ sourceKPFiniteWindow K (S.erase P) ↔
      x ∈ P.adicCompletionIntegers K ∧ r.val ∈ sourceKPFiniteWindow K S := by
  classical
  have hP : P ∉ S.erase P := Finset.notMem_erase P S
  constructor
  · intro h
    obtain ⟨hx, hr⟩ := (sourceKPFiniteWindow_single_add K (S.erase P) P x r).mp h
    exact ⟨hx hP, (sourceKPFiniteWindow_remainder_erase K S P r).mp hr⟩
  · rintro ⟨hx, hr⟩
    exact (sourceKPFiniteWindow_single_add K (S.erase P) P x r).mpr
      ⟨fun _ => hx, (sourceKPFiniteWindow_remainder_erase K S P r).mpr hr⟩

end
end ArtinMatthews
