module

public import ArtinMatthews.GiantPrimeLifespanInverse


set_option backward.privateInPublic true
@[expose] public section

/-! Exact congruence of the represented endpoints and active offsets
is sufficient for the literal raw weight to be nonzero. -/

namespace ArtinMatthews

open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

theorem giantSignedResidueLifespanWeight_ne_zero_of_view (p : ℕ) (hp : 0 < p) {n : ℕ}
    (offset : Fin n → ℤ) (q : Fin n → ℝ) (A : Finset (Fin n))
    (c : GiantSignedResidueLifespanChoice A) {L : GiantSignedPrimeLifespanInterval A}
    (hview : giantSignedPrimeLifespanView A c = some L)
    (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1)
    (hoffEnd : (offset L.finish : ZMod p) = (offset L.start : ZMod p))
    (hoffActive : ∀ i ∈ A, (offset i : ZMod p) = (offset L.start : ZMod p)) :
    giantSignedResidueLifespanWeight p offset q A c ≠ 0 := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hcost : 1 / (p : ℝ) ≠ 0 := div_ne_zero one_ne_zero hpR
  have hloss (i : Fin n) : -(1 - q i) ≠ 0 :=
    neg_ne_zero.mpr (sub_ne_zero.mpr (ne_of_gt (hq1 i)))
  have hprod (s : Finset (Fin n)) (a : Fin n) : (∏ i ∈ s, giantSignedPrimeDamping p offset q i a) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    rw [giantSignedPrimeDamping_eq]
    split_ifs
    · exact (hq0 i).ne'
    · exact one_ne_zero
  by_cases hA : A.Nonempty
  · let e := giantSignedResidueLifespanActiveEquiv A hA c
    have hL : giantSignedActiveLifespanInterval A hA e = L :=
      Option.some.inj ((giantSignedPrimeLifespanView_active A c hA).symm.trans hview)
    have hmin := hoffActive _ (A.min'_mem hA)
    have hcompatible : GiantSignedPrimeActiveCompatible p offset A (A.min' hA) :=
      fun i hi => (hoffActive i hi).trans hmin.symm
    have hstart : (offset (giantSignedPrimeStart (A.min' hA) e.1) : ZMod p) =
        (offset (A.min' hA) : ZMod p) :=
      (congrArg (fun K : GiantSignedPrimeLifespanInterval A => (offset K.start : ZMod p)) hL).trans hmin.symm
    have hfinish : (offset (giantSignedPrimeEnd (A.max' hA) e.2) : ZMod p) =
        (offset (A.min' hA) : ZMod p) :=
      (congrArg (fun K : GiantSignedPrimeLifespanInterval A => (offset K.finish : ZMod p)) hL).trans
        (hoffEnd.trans hmin.symm)
    have hb : giantSignedPrimeBirthCoefficient p offset q (A.min' hA) e.1 ≠ 0 := by
      cases hl : e.1 with
      | none => exact one_ne_zero
      | some l =>
        have hh : (offset l.val : ZMod p) = (offset (A.min' hA) : ZMod p) := by
          simpa only [hl, giantSignedPrimeStart] using hstart
        simpa only [hl, giantSignedPrimeBirthCoefficient, giantSignedPrimeOffsetHit, hh, ite_true, mul_one] using
          hloss l.val
    have hd : giantSignedPrimeTerminationCoefficient p offset q (A.min' hA) (A.max' hA) e.2 ≠ 0 := by
      cases hu : e.2 with
      | none => exact one_ne_zero
      | some u =>
        have hh : (offset u.val : ZMod p) = (offset (A.min' hA) : ZMod p) := by
          simpa only [hu, giantSignedPrimeEnd] using hfinish
        simpa only [hu, giantSignedPrimeTerminationCoefficient, giantSignedPrimeOffsetHit, hh, ite_true, mul_one] using
          hloss u.val
    rw [giantSignedResidueLifespanWeight, dite_eq_left hA]
    change (1 / (p : ℝ)) * giantSignedPrimeActiveEndpointWeight p offset q A hA e ≠ 0
    rw [giantSignedPrimeActiveEndpointWeight_interval, ite_eq_left hcompatible]
    exact mul_ne_zero hcost (mul_ne_zero (mul_ne_zero hb hd) (hprod _ _))
  · cases he : giantSignedResidueLifespanInactiveEquiv A hA c with
    | none =>
      rw [giantSignedPrimeLifespanView_inactive A c hA, he, Option.map_none] at hview
      cases hview
    | some e =>
      have hL : giantSignedOrphanLifespanInterval A hA e = L := by
        apply Option.some.inj
        simpa only [giantSignedPrimeLifespanView_inactive A c hA, he, Option.map_some] using hview
      have hhit : (offset e.2.1 : ZMod p) = (offset e.1 : ZMod p) := by
        change (offset (giantSignedOrphanLifespanInterval A hA e).finish : ZMod p) =
          (offset (giantSignedOrphanLifespanInterval A hA e).start : ZMod p)
        rw [hL]
        exact hoffEnd
      rw [giantSignedResidueLifespanWeight, dite_eq_right hA, he, Option.elim_some]
      apply mul_ne_zero hcost
      simp only [giantSignedPrimeOrphanEndpointWeight, giantSignedPrimeOrphanWeight,
        giantSignedPrimeOffsetHit, hhit, ite_true, mul_one]
      exact mul_ne_zero (mul_ne_zero (hloss _) (hloss _)) (hprod _ _)

theorem giantSignedResidueLifespanWeight_ne_zero_iff_of_view (p : ℕ) (hp : 0 < p) {n : ℕ}
    (offset : Fin n → ℤ) (q : Fin n → ℝ) (A : Finset (Fin n))
    (c : GiantSignedResidueLifespanChoice A) {L : GiantSignedPrimeLifespanInterval A}
    (hview : giantSignedPrimeLifespanView A c = some L)
    (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1) :
    giantSignedResidueLifespanWeight p offset q A c ≠ 0 ↔
      (offset L.finish : ZMod p) = (offset L.start : ZMod p) ∧
        ∀ i ∈ A, (offset i : ZMod p) = (offset L.start : ZMod p) :=
  ⟨fun hw => giantSignedPrimeLifespanView_offsets_of_weight_ne_zero p offset q A c hw hview,
    fun h => giantSignedResidueLifespanWeight_ne_zero_of_view p hp offset q A c hview hq0 hq1 h.1 h.2⟩

end
end ArtinMatthews
