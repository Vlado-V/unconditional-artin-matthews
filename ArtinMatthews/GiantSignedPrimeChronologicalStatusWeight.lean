module

public import ArtinMatthews.GiantSignedPrimeStatusVisits


set_option backward.privateInPublic true
@[expose] public section

/-! The literal chronological product contracts to the chosen prime lifespan row. -/

namespace ArtinMatthews

open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

private def isInternal {n : ℕ} {S : Finset (Fin n)}
    (L : GiantSignedPrimeLifespanInterval S) (i : Fin n) : Prop :=
  L.start < i ∧ i < L.finish ∧ i ∉ S

private theorem pendingBefore_of_view {n : ℕ} {S : Finset (Fin n)}
    (choice : GiantSignedResidueLifespanChoice S) {L : GiantSignedPrimeLifespanInterval S}
    (hview : giantSignedPrimeLifespanView S choice = some L) (i : Fin n) :
    giantSignedPrimePendingBefore choice i ↔ isInternal L i ∨ giantSignedPrimeGhostDeathAt choice i := by
  simp only [giantSignedPrimePendingBefore, giantSignedPrimeGhostDeathAt, hview,
    Option.elim_some, isInternal]
  constructor
  · rintro ⟨hl, hu, hi⟩
    rcases lt_or_eq_of_le hu with hlt | he
    · exact Or.inl ⟨hl, hlt, hi⟩
    · exact Or.inr ⟨he.symm, L.ghostDeath_iff.mpr (he ▸ hi)⟩
  · rintro (⟨hl, hu, hi⟩ | ⟨he, hd⟩)
    · exact ⟨hl, hu.le, hi⟩
    · exact ⟨he ▸ L.ghostDeath_strict hd, he.ge, he ▸ L.ghostDeath_iff.mp hd⟩

private theorem pendingAfter_of_view {n : ℕ} {S : Finset (Fin n)}
    (choice : GiantSignedResidueLifespanChoice S) {L : GiantSignedPrimeLifespanInterval S}
    (hview : giantSignedPrimeLifespanView S choice = some L) (i : Fin n) :
    giantSignedPrimePendingAfter choice i ↔ isInternal L i ∨ giantSignedPrimeGhostBirthAt choice i := by
  simp only [giantSignedPrimePendingAfter, giantSignedPrimeGhostBirthAt, hview,
    Option.elim_some, isInternal]
  constructor
  · rintro ⟨hl, hu, hi⟩
    rcases lt_or_eq_of_le hl with hlt | he
    · exact Or.inl ⟨hlt, hu, hi⟩
    · exact Or.inr ⟨he, L.ghostBirth_iff.mpr (he.symm ▸ hi)⟩
  · rintro (⟨hl, hu, hi⟩ | ⟨he, hb⟩)
    · exact ⟨hl.le, hu, hi⟩
    · exact ⟨he.le, he ▸ L.ghostBirth_strict hb, he ▸ L.ghostBirth_iff.mp hb⟩

variable {P : Finset ℕ} {n : ℕ} {A : (p : P) → Finset (Fin n)}
    (c : (p : P) → GiantSignedResidueLifespanChoice (A p))

private theorem join_one_visit (V ρ : ℝ) (offset : Fin n → ℤ) (q : Fin n → ℝ) (p : P)
    (hw : giantSignedResidueLifespanWeight p.val offset q (A p) (c p) ≠ 0)
    {L : GiantSignedPrimeLifespanInterval (A p)}
    (hview : giantSignedPrimeLifespanView (A p) (c p) = some L) (i : Fin n) :
    (giantSignedPrimeVisitGhostFactor c V ρ offset q i p *
      giantSignedPrimeAfterHalf c ρ offset i p) * giantSignedPrimeBeforeHalf c ρ offset i p =
      ((if giantSignedPrimeGhostBirthAt (c p) i then
          ((giantSignedRowC (q i) V ρ * ρ * giantSignedRowBirthAtom V p.val q : ℝ) : ℂ) else 1) *
        (if isInternal L i then
          (giantSignedRowInternalDamping ρ p.val offset q i L.start : ℂ) else 1)) *
        (if giantSignedPrimeGhostDeathAt (c p) i then ((ρ * giantSignedRowD (q i) ρ : ℝ) : ℂ) else 1) := by
  have hBefore := pendingBefore_of_view (c p) hview i
  have hAfter := pendingAfter_of_view (c p) hview i
  have hres : giantSignedLifespanResidue c offset i p = 0 ↔
      (offset i : ZMod p.val) = (offset L.start : ZMod p.val) := by
    rw [giantSignedLifespanResidue, hview, Option.elim_some, sub_eq_zero]
  have hEnds := giantSignedPrimeGhostEndpoints_disjoint (c p) i
  unfold giantSignedPrimeVisitGhostFactor giantSignedGhostVisitPrimeFactor
    giantSignedGhostVisitRetainedZero giantSignedPrimeAfterHalf giantSignedPrimeBeforeHalf
  by_cases hb : giantSignedPrimeGhostBirthAt (c p) i
  · have hd : ¬giantSignedPrimeGhostDeathAt (c p) i := fun hd => hEnds ⟨hb, hd⟩
    have hi : ¬isInternal L i := fun hi =>
      (giantSignedPrimeGhostBirthAt_not_pendingBefore (c p) i hb) (hBefore.mpr (Or.inl hi))
    have hz := giantSignedLifespanResidue_ghostBirth c offset i p hb
    simp [hBefore, hAfter, hb, hd, hi, hz] <;> ring
  · by_cases hd : giantSignedPrimeGhostDeathAt (c p) i
    · have hi : ¬isInternal L i := by
        have he : L.finish = i ∧ L.ghostDeath = true := by
          simpa only [giantSignedPrimeGhostDeathAt, hview, Option.elim_some] using hd
        exact fun hi => not_lt_of_ge he.1.le hi.2.1
      have hz := giantSignedLifespanResidue_ghostDeath c offset q i p hw hd
      simp [hBefore, hAfter, hb, hd, hi, hz] <;> ring
    · by_cases hi : isInternal L i
      · by_cases he : (offset i : ZMod p.val) = (offset L.start : ZMod p.val)
        · simp [hBefore, hAfter, hb, hd, hi, hres.mpr he, giantSignedRowInternalDamping, he,
            mul_assoc, mul_left_comm, mul_comm]
        · have hz : giantSignedLifespanResidue c offset i p ≠ 0 := fun h => he (hres.mp h)
          simp [hBefore, hAfter, hb, hd, hi, hz, giantSignedRowInternalDamping, he]
      · simp [hBefore, hAfter, hb, hd, hi]

private theorem cast_prod {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ((∏ i ∈ s, f i : ℝ) : ℂ) = ∏ i ∈ s, (f i : ℂ) :=
  map_prod Complex.ofRealHom f s

theorem giantSignedPrimeChronologicalStatusProduct_some {N : ℕ}
    {active : (p : P) → Finset (Fin (N + 1))}
    (choices : (p : P) → GiantSignedResidueLifespanChoice (active p)) (V ρ : ℝ)
    (offset : Fin (N + 1) → ℤ) (q : Fin (N + 1) → ℝ) (p : P)
    (hw : giantSignedResidueLifespanWeight p.val offset q (active p) (choices p) ≠ 0)
    {L : GiantSignedPrimeLifespanInterval (active p)}
    (hview : giantSignedPrimeLifespanView (active p) (choices p) = some L) :
    giantSignedPrimeChronologicalStatusProduct choices V ρ offset q p =
      (if L.ghostBirth = true then
        (((V⁻¹) ^ giantSignedActiveRunCount (active p) : ℝ) : ℂ)
      else ((giantSignedRowBirthAtom V p.val q *
        (V⁻¹) ^ (giantSignedActiveRunCount (active p) - 1) : ℝ) : ℂ)) *
      (if L.ghostBirth = true then
        ((giantSignedRowC (q L.start) V ρ * ρ * giantSignedRowBirthAtom V p.val q : ℝ) : ℂ) else 1) *
      (∏ i ∈ Finset.univ.filter (fun i => L.start < i ∧ i < L.finish ∧ i ∉ active p),
        (giantSignedRowInternalDamping ρ p.val offset q i L.start : ℂ)) *
      (if L.ghostDeath = true then ((ρ * giantSignedRowD (q L.finish) ρ : ℝ) : ℂ) else 1) := by
  rw [giantSignedPrimeChronologicalStatusProduct_eq_visits,
    giantSignedPrimeVisitRunFactor_product_of_view V (giantSignedRowBirthAtom V p.val q) (choices p) hview]
  simp_rw [join_one_visit choices V ρ offset q p hw hview]
  have hb :
      (∏ i, if giantSignedPrimeGhostBirthAt (choices p) i then
        ((giantSignedRowC (q i) V ρ * ρ * giantSignedRowBirthAtom V p.val q : ℝ) : ℂ) else 1) =
      if L.ghostBirth = true then
        ((giantSignedRowC (q L.start) V ρ * ρ * giantSignedRowBirthAtom V p.val q : ℝ) : ℂ) else 1 := by
    simp_rw [giantSignedPrimeGhostBirthAt, hview, Option.elim_some]
    by_cases h : L.ghostBirth = true
    · simp only [h, and_true, ite_true, Fintype.prod_ite_eq]
    · simp [h]
  have hd :
      (∏ i, if giantSignedPrimeGhostDeathAt (choices p) i then
        ((ρ * giantSignedRowD (q i) ρ : ℝ) : ℂ) else 1) =
      if L.ghostDeath = true then ((ρ * giantSignedRowD (q L.finish) ρ : ℝ) : ℂ) else 1 := by
    simp_rw [giantSignedPrimeGhostDeathAt, hview, Option.elim_some]
    by_cases h : L.ghostDeath = true
    · simp only [h, and_true, ite_true, Fintype.prod_ite_eq]
    · simp [h]
  simp only [Finset.prod_mul_distrib, hb, hd, Finset.prod_filter, isInternal]
  ac_rfl

private theorem active_birth_rows (V ρ : ℝ) (offset : Fin n → ℤ) (q : Fin n → ℝ) (p : P)
    (hA : (A p).Nonempty) (e : GiantSignedPrimeActiveEndpointChoice (A p) hA)
    (hstart : (offset (giantSignedActiveLifespanInterval (A p) hA e).start : ZMod p.val) =
      (offset ((A p).min' hA) : ZMod p.val)) :
    (if (giantSignedActiveLifespanInterval (A p) hA e).ghostBirth = true then
        (((V⁻¹) ^ giantSignedActiveRunCount (A p) : ℝ) : ℂ)
      else ((giantSignedRowBirthAtom V p.val q *
        (V⁻¹) ^ (giantSignedActiveRunCount (A p) - 1) : ℝ) : ℂ)) *
      (if (giantSignedActiveLifespanInterval (A p) hA e).ghostBirth = true then
        ((giantSignedRowC (q (giantSignedActiveLifespanInterval (A p) hA e).start) V ρ *
          ρ * giantSignedRowBirthAtom V p.val q : ℝ) : ℂ) else 1) =
      (giantSignedActiveBirthRows V ρ p.val offset q (A p) hA e.1 : ℂ) := by
  cases he : e.1 with
  | none =>
    simp [giantSignedActiveLifespanInterval, he, giantSignedActiveBirthRows]
  | some l =>
    have hl : (offset l.val : ZMod p.val) = (offset ((A p).min' hA) : ZMod p.val) := by
      simpa only [giantSignedActiveLifespanInterval, he, giantSignedPrimeStart] using hstart
    simp [giantSignedActiveLifespanInterval, he, giantSignedPrimeStart, giantSignedActiveBirthRows,
      giantSignedPrimeOffsetHit, hl] <;> ring

private theorem active_death_rows (ρ : ℝ) (offset : Fin n → ℤ) (q : Fin n → ℝ) (p : P)
    (hA : (A p).Nonempty) (e : GiantSignedPrimeActiveEndpointChoice (A p) hA)
    (hfinish : (offset (giantSignedActiveLifespanInterval (A p) hA e).finish : ZMod p.val) =
      (offset ((A p).min' hA) : ZMod p.val)) :
    (if (giantSignedActiveLifespanInterval (A p) hA e).ghostDeath = true then
        ((ρ * giantSignedRowD (q (giantSignedActiveLifespanInterval (A p) hA e).finish) ρ : ℝ) : ℂ)
      else 1) =
      (giantSignedActiveTerminationRows ρ p.val offset q (A p) hA e.2 : ℂ) := by
  cases he : e.2 with
  | none =>
    simp [giantSignedActiveLifespanInterval, he, giantSignedActiveTerminationRows]
  | some u =>
    have hu : (offset u.val : ZMod p.val) = (offset ((A p).min' hA) : ZMod p.val) := by
      simpa only [giantSignedActiveLifespanInterval, he, giantSignedPrimeEnd] using hfinish
    simp [giantSignedActiveLifespanInterval, he, giantSignedPrimeEnd, giantSignedActiveTerminationRows,
      giantSignedPrimeOffsetHit, hu]

theorem giantSignedPrimeChronologicalStatusProduct_eq_rowWeight {N : ℕ}
    {active : (p : P) → Finset (Fin (N + 1))}
    (choices : (p : P) → GiantSignedResidueLifespanChoice (active p)) (V ρ : ℝ)
    (offset : Fin (N + 1) → ℤ) (q : Fin (N + 1) → ℝ) (p : P)
    (hw : giantSignedResidueLifespanWeight p.val offset q (active p) (choices p) ≠ 0) :
    giantSignedPrimeChronologicalStatusProduct choices V ρ offset q p =
      (giantSignedPrimeRowWeight V ρ p.val offset q (active p) (choices p) : ℂ) := by
  by_cases hA : (active p).Nonempty
  · let e := giantSignedResidueLifespanActiveEquiv (active p) hA (choices p)
    let L := giantSignedActiveLifespanInterval (active p) hA e
    have hview : giantSignedPrimeLifespanView (active p) (choices p) = some L :=
      giantSignedPrimeLifespanView_active (active p) (choices p) hA
    have hOff := giantSignedPrimeLifespanView_offsets_of_weight_ne_zero
      p.val offset q (active p) (choices p) hw hview
    have hstart : (offset L.start : ZMod p.val) = (offset ((active p).min' hA) : ZMod p.val) :=
      (hOff.2 _ ((active p).min'_mem hA)).symm
    have hfinish : (offset L.finish : ZMod p.val) = (offset ((active p).min' hA) : ZMod p.val) :=
      hOff.1.trans hstart
    have hcompatible : GiantSignedPrimeActiveCompatible p.val offset (active p) ((active p).min' hA) :=
      fun i hi => (hOff.2 i hi).trans hstart
    have hdamp (i : Fin (N + 1)) : giantSignedRowInternalDamping ρ p.val offset q i L.start =
        giantSignedRowInternalDamping ρ p.val offset q i ((active p).min' hA) := by
      unfold giantSignedRowInternalDamping
      rw [hstart]
    rw [giantSignedPrimeChronologicalStatusProduct_some choices V ρ offset q p hw hview]
    rw [active_birth_rows V ρ offset q p hA e hstart, active_death_rows ρ offset q p hA e hfinish]
    rw [giantSignedPrimeRowWeight, dite_eq_left hA]
    change _ = (giantSignedActiveRowWeight V ρ p.val offset q (active p) hA e : ℂ)
    rw [giantSignedActiveRowWeight, ite_eq_left hcompatible]
    simp only [Complex.ofReal_mul, cast_prod]
    simp_rw [hdamp]
    simp only [L, giantSignedActiveLifespanInterval]
  · let e := giantSignedResidueLifespanInactiveEquiv (active p) hA (choices p)
    have hEmpty := Finset.not_nonempty_iff_eq_empty.mp hA
    have hview := giantSignedPrimeLifespanView_inactive (active p) (choices p) hA
    have hrow : giantSignedPrimeRowWeight V ρ p.val offset q (active p) (choices p) =
        e.elim 1 (giantSignedOrphanRowWeight V ρ p.val offset q) := by
      rw [giantSignedPrimeRowWeight, dite_eq_right hA]
    cases he : e with
    | none =>
      have hnone : giantSignedPrimeLifespanView (active p) (choices p) = none := by
        change _ = e.map (giantSignedOrphanLifespanInterval (active p) hA) at hview
        simpa only [he, Option.map_none] using hview
      rw [giantSignedPrimeChronologicalStatusProduct_none choices V ρ offset q p hnone, hrow, he]
      simp only [Option.elim_none, Complex.ofReal_one]
    | some orphan =>
      let L := giantSignedOrphanLifespanInterval (active p) hA orphan
      have hsome : giantSignedPrimeLifespanView (active p) (choices p) = some L := by
        change _ = e.map (giantSignedOrphanLifespanInterval (active p) hA) at hview
        simpa only [he, Option.map_some, L] using hview
      have hOff := giantSignedPrimeLifespanView_offsets_of_weight_ne_zero
        p.val offset q (active p) (choices p) hw hsome
      have heq : (offset orphan.2.1 : ZMod p.val) = (offset orphan.1 : ZMod p.val) := hOff.1
      have hr : giantSignedActiveRunCount (active p) = 0 := by
        rw [hEmpty, giantSignedActiveRunCount_empty]
      rw [giantSignedPrimeChronologicalStatusProduct_some choices V ρ offset q p hw hsome, hrow, he]
      simp [L, giantSignedOrphanLifespanInterval, hr, hEmpty, giantSignedOrphanRowWeight,
        giantSignedPrimeOffsetHit, heq, cast_prod]

theorem giantSignedPrimeChronologicalStatusProduct_eq {N : ℕ}
    {active : (p : P) → Finset (Fin (N + 1))}
    (choices : (p : P) → GiantSignedResidueLifespanChoice (active p)) (V ρ : ℝ)
    (hV : V ≠ 0) (hρ : ρ ≠ 0) (offset : Fin (N + 1) → ℤ) (q : Fin (N + 1) → ℝ) (p : P)
    (hw : giantSignedResidueLifespanWeight p.val offset q (active p) (choices p) ≠ 0)
    (hb : giantSignedPrimeResidueBaseline p.val q ≠ 0) :
    giantSignedPrimeChronologicalStatusProduct choices V ρ offset q p =
      (((V⁻¹) ^ giantSignedActiveRunCount (active p) *
        (giantSignedResidueLifespanWeight p.val offset q (active p) (choices p) /
          giantSignedPrimeResidueBaseline p.val q) : ℝ) : ℂ) := by
  rw [giantSignedPrimeChronologicalStatusProduct_eq_rowWeight choices V ρ offset q p hw,
    giantSignedPrimeRowWeight_eq V ρ hV hρ p.val offset q (active p) (choices p) hb]

end

end ArtinMatthews
