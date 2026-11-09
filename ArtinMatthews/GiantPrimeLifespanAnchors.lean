module

public import ArtinMatthews.GiantPrimeLifespanView


set_option backward.privateInPublic true
@[expose] public section

/-! The nonzero residue weight fixes the anchor of every represented lifespan. -/

namespace ArtinMatthews

noncomputable section

theorem giantSignedPrimeLifespanView_offsets_of_weight_ne_zero (p : ℕ) {n : ℕ}
    (offset : Fin n → ℤ) (q : Fin n → ℝ) (A : Finset (Fin n))
    (c : GiantSignedResidueLifespanChoice A)
    (hweight : giantSignedResidueLifespanWeight p offset q A c ≠ 0)
    {L : GiantSignedPrimeLifespanInterval A}
    (hview : giantSignedPrimeLifespanView A c = some L) :
    (offset L.finish : ZMod p) = (offset L.start : ZMod p) ∧
      ∀ i ∈ A, (offset i : ZMod p) = (offset L.start : ZMod p) := by
  by_cases hA : A.Nonempty
  · let e := giantSignedResidueLifespanActiveEquiv A hA c
    have hL : giantSignedActiveLifespanInterval A hA e = L :=
      Option.some.inj ((giantSignedPrimeLifespanView_active A c hA).symm.trans hview)
    have hscaled : (1 / (p : ℝ)) * giantSignedPrimeActiveEndpointWeight p offset q A hA e ≠ 0 := by
      simpa only [giantSignedResidueLifespanWeight, dite_eq_left hA, e] using hweight
    have he := (mul_ne_zero_iff.mp hscaled).2
    have hends := giantSignedPrimeActiveEndpointWeight_endpoints p offset q A hA e he
    have hactive := giantSignedPrimeActiveEndpointWeight_compatible p offset q A hA e he
    rw [← hL]
    exact ⟨hends.2.trans hends.1.symm, fun i hi => (hactive i hi).trans hends.1.symm⟩
  · cases heq : giantSignedResidueLifespanInactiveEquiv A hA c with
    | none =>
      simp [giantSignedPrimeLifespanView_inactive A c hA, heq] at hview
    | some e =>
      have hL : giantSignedOrphanLifespanInterval A hA e = L := by
        apply Option.some.inj
        simpa only [giantSignedPrimeLifespanView_inactive A c hA, heq, Option.map_some] using hview
      have hscaled : (1 / (p : ℝ)) * giantSignedPrimeOrphanEndpointWeight p offset q e ≠ 0 := by
        simpa only [giantSignedResidueLifespanWeight, dite_eq_right hA, heq, Option.elim_some] using hweight
      have he := (mul_ne_zero_iff.mp hscaled).2
      rw [← hL]
      exact ⟨giantSignedPrimeOrphanEndpointWeight_endpoints p offset q e he,
        fun i hi => (hA ⟨i, hi⟩).elim⟩

theorem giantSignedPrimeLifespanView_none_weight (p : ℕ) {n : ℕ}
    (offset : Fin n → ℤ) (q : Fin n → ℝ) (A : Finset (Fin n))
    (c : GiantSignedResidueLifespanChoice A)
    (hview : giantSignedPrimeLifespanView A c = none) :
    A = ∅ ∧ giantSignedResidueLifespanWeight p offset q A c = giantSignedPrimeResidueBaseline p q := by
  have hA := giantSignedPrimeLifespanView_none_empty A c hview
  have hn := Finset.not_nonempty_iff_eq_empty.mpr hA
  have he : giantSignedResidueLifespanInactiveEquiv A hn c = none := by
    cases heq : giantSignedResidueLifespanInactiveEquiv A hn c with
    | none => rfl
    | some e =>
      simp [giantSignedPrimeLifespanView_inactive A c hn, heq] at hview
  exact ⟨hA, by simp only [giantSignedResidueLifespanWeight, dite_eq_right hn, he, Option.elim_none]⟩

end

end ArtinMatthews
