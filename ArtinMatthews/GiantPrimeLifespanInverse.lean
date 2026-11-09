module

public import ArtinMatthews.GiantPrimeLifespanAnchors


set_option backward.privateInPublic true
@[expose] public section

/-! The literal lifespan view determines its original finite endpoint choice. -/

namespace ArtinMatthews

noncomputable section
attribute [local instance] Classical.propDecidable

variable {n : ℕ} {A : Finset (Fin n)}

theorem giantSignedPrimeLifespanInterval_ext {L R : GiantSignedPrimeLifespanInterval A}
    (hs : L.start = R.start) (hf : L.finish = R.finish) : L = R := by
  have hb : L.ghostBirth = R.ghostBirth := by
    apply Bool.eq_iff_iff.mpr
    change L.ghostBirth = true ↔ R.ghostBirth = true
    rw [L.ghostBirth_iff, R.ghostBirth_iff, hs]
  have hd : L.ghostDeath = R.ghostDeath := by
    apply Bool.eq_iff_iff.mpr
    change L.ghostDeath = true ↔ R.ghostDeath = true
    rw [L.ghostDeath_iff, R.ghostDeath_iff, hf]
  cases L
  cases R
  cases hs
  cases hf
  cases hb
  cases hd
  rfl

private def activeEndpointsOfInterval (hA : A.Nonempty) (L : GiantSignedPrimeLifespanInterval A) :
    GiantSignedPrimeActiveEndpointChoice A hA :=
  ⟨if h : L.start = A.min' hA then none else
      some ⟨L.start, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        lt_of_le_of_ne (L.active_contained _ (A.min'_mem hA)).1 h⟩⟩,
    if h : L.finish = A.max' hA then none else
      some ⟨L.finish, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        lt_of_le_of_ne (L.active_contained _ (A.max'_mem hA)).2 (fun he => h he.symm)⟩⟩⟩

private def orphanEndpointsOfInterval (hA : ¬A.Nonempty) (L : GiantSignedPrimeLifespanInterval A) :
    GiantSignedPrimeOrphanEndpointChoice n :=
  ⟨L.start, ⟨L.finish, Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, (giantSignedPrimeLifespanInterval_orphan L hA).1⟩⟩⟩

def giantSignedResidueLifespanChoiceOfInterval (L : GiantSignedPrimeLifespanInterval A) :
    GiantSignedResidueLifespanChoice A :=
  if hA : A.Nonempty then
    (giantSignedResidueLifespanActiveEquiv A hA).symm (activeEndpointsOfInterval hA L)
  else
    (giantSignedResidueLifespanInactiveEquiv A hA).symm (some (orphanEndpointsOfInterval hA L))

def giantSignedResidueLifespanAbsentChoice (hA : ¬A.Nonempty) : GiantSignedResidueLifespanChoice A :=
  (giantSignedResidueLifespanInactiveEquiv A hA).symm none

theorem giantSignedPrimeLifespanView_choiceOfInterval (L : GiantSignedPrimeLifespanInterval A) :
    giantSignedPrimeLifespanView A (giantSignedResidueLifespanChoiceOfInterval L) = some L := by
  by_cases hA : A.Nonempty
  · rw [giantSignedPrimeLifespanView_active A _ hA, giantSignedResidueLifespanChoiceOfInterval,
      dite_eq_left hA, Equiv.apply_symm_apply]
    apply congrArg some
    apply giantSignedPrimeLifespanInterval_ext
    · change giantSignedPrimeStart (A.min' hA) (activeEndpointsOfInterval hA L).1 = L.start
      simp only [activeEndpointsOfInterval]
      split_ifs with he
      · exact he.symm
      · rfl
    · change giantSignedPrimeEnd (A.max' hA) (activeEndpointsOfInterval hA L).2 = L.finish
      simp only [activeEndpointsOfInterval]
      split_ifs with he
      · exact he.symm
      · rfl
  · rw [giantSignedPrimeLifespanView_inactive A _ hA, giantSignedResidueLifespanChoiceOfInterval,
      dite_eq_right hA, Equiv.apply_symm_apply, Option.map_some]
    exact congrArg some (giantSignedPrimeLifespanInterval_ext rfl rfl)

theorem giantSignedPrimeLifespanView_absentChoice (hA : ¬A.Nonempty) :
    giantSignedPrimeLifespanView A (giantSignedResidueLifespanAbsentChoice hA) = none := by
  rw [giantSignedPrimeLifespanView_inactive A _ hA, giantSignedResidueLifespanAbsentChoice,
    Equiv.apply_symm_apply, Option.map_none]

private theorem option_endpoint_injective {s : Finset (Fin n)} {a : Fin n} (ha : a ∉ s) :
    Function.Injective (fun c : Option ↥s => c.elim a Subtype.val) := by
  intro c d he
  cases c with
  | none =>
    cases d with
    | none => rfl
    | some d =>
      have h : a = d.val := he
      exact (ha (h.symm ▸ d.property)).elim
  | some c =>
    cases d with
    | none =>
      have h : c.val = a := he
      exact (ha (h ▸ c.property)).elim
    | some d => exact congrArg some (Subtype.ext he)

private theorem active_interval_injective (hA : A.Nonempty) :
    Function.Injective (giantSignedActiveLifespanInterval A hA) := by
  intro c d he
  have hs : A.min' hA ∉ Finset.univ.filter (fun l : Fin n => l < A.min' hA) :=
    fun h => (lt_irrefl _) (Finset.mem_filter.mp h).2
  have hf : A.max' hA ∉ Finset.univ.filter (fun u : Fin n => A.max' hA < u) :=
    fun h => (lt_irrefl _) (Finset.mem_filter.mp h).2
  have hStart (x : GiantSignedPrimePrefixChoice (A.min' hA)) :
      giantSignedPrimeStart (A.min' hA) x = x.elim (A.min' hA) Subtype.val := by cases x <;> rfl
  have hFinish (x : GiantSignedPrimeSuffixChoice (A.max' hA)) :
      giantSignedPrimeEnd (A.max' hA) x = x.elim (A.max' hA) Subtype.val := by cases x <;> rfl
  have hleft : giantSignedPrimeStart (A.min' hA) c.1 = giantSignedPrimeStart (A.min' hA) d.1 :=
    congrArg GiantSignedPrimeLifespanInterval.start he
  have hright : giantSignedPrimeEnd (A.max' hA) c.2 = giantSignedPrimeEnd (A.max' hA) d.2 :=
    congrArg GiantSignedPrimeLifespanInterval.finish he
  simp only [hStart] at hleft
  simp only [hFinish] at hright
  exact Prod.ext (option_endpoint_injective hs hleft) (option_endpoint_injective hf hright)

private theorem orphan_interval_injective (hA : ¬A.Nonempty) :
    Function.Injective (giantSignedOrphanLifespanInterval A hA) := by
  rintro ⟨l, ⟨u, hu⟩⟩ ⟨l', ⟨u', hu'⟩⟩ he
  have hl : l = l' := congrArg GiantSignedPrimeLifespanInterval.start he
  have hf : u = u' := congrArg GiantSignedPrimeLifespanInterval.finish he
  subst l'
  subst u'
  rfl

theorem giantSignedPrimeLifespanView_injective (A : Finset (Fin n)) :
    Function.Injective (giantSignedPrimeLifespanView A) := by
  intro c d he
  by_cases hA : A.Nonempty
  · rw [giantSignedPrimeLifespanView_active A c hA, giantSignedPrimeLifespanView_active A d hA] at he
    exact (giantSignedResidueLifespanActiveEquiv A hA).injective
      (active_interval_injective hA (Option.some.inj he))
  · rw [giantSignedPrimeLifespanView_inactive A c hA, giantSignedPrimeLifespanView_inactive A d hA] at he
    exact (giantSignedResidueLifespanInactiveEquiv A hA).injective
      (Option.map_injective (orphan_interval_injective hA) he)

theorem giantSignedResidueLifespanChoiceOfInterval_eq_of_view (c : GiantSignedResidueLifespanChoice A)
    {L : GiantSignedPrimeLifespanInterval A} (hview : giantSignedPrimeLifespanView A c = some L) :
    giantSignedResidueLifespanChoiceOfInterval L = c :=
  giantSignedPrimeLifespanView_injective A ((giantSignedPrimeLifespanView_choiceOfInterval L).trans hview.symm)

theorem giantSignedResidueLifespanAbsentChoice_eq_of_view (hA : ¬A.Nonempty)
    (c : GiantSignedResidueLifespanChoice A) (hview : giantSignedPrimeLifespanView A c = none) :
    giantSignedResidueLifespanAbsentChoice hA = c :=
  giantSignedPrimeLifespanView_injective A ((giantSignedPrimeLifespanView_absentChoice hA).trans hview.symm)

theorem giantSignedResidueLifespanAbsentChoice_weight (p : ℕ) (offset : Fin n → ℤ) (q : Fin n → ℝ)
    (hA : ¬A.Nonempty) :
    giantSignedResidueLifespanWeight p offset q A (giantSignedResidueLifespanAbsentChoice hA) =
      giantSignedPrimeResidueBaseline p q :=
  (giantSignedPrimeLifespanView_none_weight p offset q A _ (giantSignedPrimeLifespanView_absentChoice hA)).2

end
end ArtinMatthews
