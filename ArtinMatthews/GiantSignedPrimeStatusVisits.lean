module

public import ArtinMatthews.GiantSignedGhostVisitCoefficient
public import ArtinMatthews.GiantPrimeRowWeight


set_option backward.privateInPublic true
@[expose] public section

/-! The literal one-prime chronology regrouped by visits and active runs. -/

namespace ArtinMatthews

open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

variable {P : Finset ℕ} {n : ℕ} {A : (p : P) → Finset (Fin n)}
    (c : (p : P) → GiantSignedResidueLifespanChoice (A p))

def giantSignedPrimeBeforeHalf (ρ : ℝ) (offset : Fin n → ℤ) (i : Fin n) (p : P) : ℂ :=
  if giantSignedPrimePendingBefore (c p) i ∧ giantSignedLifespanResidue c offset i p = 0 then
    (ρ : ℂ) else 1

def giantSignedPrimeAfterHalf (ρ : ℝ) (offset : Fin n → ℤ) (i : Fin n) (p : P) : ℂ :=
  if giantSignedPrimePendingAfter (c p) i ∧ giantSignedLifespanResidue c offset i p = 0 then
    (ρ : ℂ) else 1

def giantSignedPrimeVisitGhostFactor (V ρ : ℝ) (offset : Fin n → ℤ)
    (q : Fin n → ℝ) (i : Fin n) (p : P) : ℂ :=
  giantSignedGhostVisitPrimeFactor c offset i (fun a => giantSignedRowBirthAtom V a.val q)
    (giantSignedRowA (q i) ρ : ℂ) (giantSignedRowC (q i) V ρ : ℂ)
    (giantSignedRowD (q i) ρ : ℂ) p

def giantSignedPrimeVisitRunFactor (V ν : ℝ) {S : Finset (Fin n)}
    (choice : GiantSignedResidueLifespanChoice S) (i : Fin n) : ℂ :=
  if i ∈ giantSignedActiveRunStarts S then
    if giantSignedPrimeFreshAt choice i then (ν : ℂ) else ((V⁻¹ : ℝ) : ℂ)
  else 1

def giantSignedPrimeChronologicalStatusProduct {N : ℕ} {active : (p : P) → Finset (Fin (N + 1))}
    (choices : (p : P) → GiantSignedResidueLifespanChoice (active p)) (V ρ : ℝ)
    (offset : Fin (N + 1) → ℤ) (q : Fin (N + 1) → ℝ) (p : P) : ℂ :=
  (if (0 : Fin (N + 1)) ∈ active p then (giantSignedRowBirthAtom V p.val q : ℂ) else 1) *
    (∏ i, giantSignedPrimeVisitGhostFactor choices V ρ offset q i p) *
    ∏ j : Fin N, (giantSignedPrimeAfterHalf choices ρ offset j.castSucc p *
      giantSignedPrimeBeforeHalf choices ρ offset j.succ p) *
      ((if giantSignedPrimePromote (choices p) j.castSucc j.succ then ((V⁻¹ : ℝ) : ℂ) else 1) *
        (if giantSignedPrimeFreshAt (choices p) j.succ then (giantSignedRowBirthAtom V p.val q : ℂ) else 1))

private theorem runStart_zero_iff {N : ℕ} (S : Finset (Fin (N + 1))) :
    (0 : Fin (N + 1)) ∈ giantSignedActiveRunStarts S ↔ (0 : Fin (N + 1)) ∈ S := by
  rw [giantSignedActiveRunStarts, Finset.mem_filter]
  refine ⟨And.left, fun h => ⟨h, ?_⟩⟩
  rintro ⟨j, _, hj⟩
  simp only [Fin.val_zero] at hj
  omega

private theorem runStart_succ_iff {N : ℕ} (S : Finset (Fin (N + 1))) (j : Fin N) :
    j.succ ∈ giantSignedActiveRunStarts S ↔ j.succ ∈ S ∧ j.castSucc ∉ S := by
  rw [giantSignedActiveRunStarts, Finset.mem_filter]
  constructor
  · rintro ⟨hs, hpred⟩
    exact ⟨hs, fun h => hpred ⟨j.castSucc, h, rfl⟩⟩
  · rintro ⟨hs, hpred⟩
    refine ⟨hs, ?_⟩
    rintro ⟨k, hk, he⟩
    have hk' : k = j.castSucc := Fin.ext (by
      simp only [Fin.val_succ, Fin.val_castSucc] at he ⊢
      omega)
    exact hpred (hk' ▸ hk)

private theorem fresh_zero_of_active {N : ℕ} {S : Finset (Fin (N + 1))}
    (choice : GiantSignedResidueLifespanChoice S) (h0 : (0 : Fin (N + 1)) ∈ S) :
    giantSignedPrimeFreshAt choice 0 := by
  obtain ⟨L, hview, hstart, _⟩ := giantSignedPrimeLifespanView_of_active S choice 0 h0
  have hs : L.start = 0 := Fin.ext (Nat.eq_zero_of_le_zero hstart)
  rw [giantSignedPrimeFreshAt, hview, Option.elim_some]
  exact ⟨hs, h0⟩

private theorem primeRunFactor_zero {N : ℕ} {S : Finset (Fin (N + 1))}
    (choice : GiantSignedResidueLifespanChoice S) (V ν : ℝ) :
    giantSignedPrimeVisitRunFactor V ν choice 0 =
      if (0 : Fin (N + 1)) ∈ S then (ν : ℂ) else 1 := by
  simp only [giantSignedPrimeVisitRunFactor, runStart_zero_iff]
  by_cases h0 : (0 : Fin (N + 1)) ∈ S
  · simp only [h0, ite_true, fresh_zero_of_active choice h0]
  · simp only [h0, ite_false]

private theorem primeRunFactor_succ {N : ℕ} {S : Finset (Fin (N + 1))}
    (choice : GiantSignedResidueLifespanChoice S) (V ν : ℝ) (j : Fin N) :
    (if giantSignedPrimePromote choice j.castSucc j.succ then ((V⁻¹ : ℝ) : ℂ) else 1) *
      (if giantSignedPrimeFreshAt choice j.succ then (ν : ℂ) else 1) =
      giantSignedPrimeVisitRunFactor V ν choice j.succ := by
  have hn := giantSignedPrimeNewActive_adjacent choice j.castSucc j.succ rfl
  have hd := giantSignedPrimePromoteFresh_disjoint choice j.castSucc j.succ rfl
  simp only [giantSignedPrimeVisitRunFactor, runStart_succ_iff, hn]
  by_cases hp : giantSignedPrimePromote choice j.castSucc j.succ
  · have hf : ¬giantSignedPrimeFreshAt choice j.succ := fun hf => hd ⟨hp, hf⟩
    simp only [hp, hf, ite_true, ite_false, true_or, mul_one]
  · by_cases hf : giantSignedPrimeFreshAt choice j.succ
    · simp only [hp, hf, ite_true, ite_false, or_true, one_mul]
    · simp only [hp, hf, ite_false, or_false, mul_one]

private theorem join_visit_product {N : ℕ} (ghost after before run : Fin (N + 1) → ℂ)
    (hAfter : after (Fin.last N) = 1) (hBefore : before 0 = 1) :
    run 0 * (∏ i, ghost i) *
      (∏ j : Fin N, (after j.castSucc * before j.succ) * run j.succ) =
      (∏ i, run i) * ∏ i, (ghost i * after i) * before i := by
  have ha := Fin.prod_univ_castSucc after
  rw [hAfter, mul_one] at ha
  have hb := Fin.prod_univ_succ before
  rw [hBefore, one_mul] at hb
  have hr := Fin.prod_univ_succ run
  simp only [Finset.prod_mul_distrib, ha, hb, hr]
  ring

theorem giantSignedPrimeChronologicalStatusProduct_eq_visits {N : ℕ}
    {active : (p : P) → Finset (Fin (N + 1))}
    (choices : (p : P) → GiantSignedResidueLifespanChoice (active p)) (V ρ : ℝ)
    (offset : Fin (N + 1) → ℤ) (q : Fin (N + 1) → ℝ) (p : P) :
    giantSignedPrimeChronologicalStatusProduct choices V ρ offset q p =
      (∏ i, giantSignedPrimeVisitRunFactor V (giantSignedRowBirthAtom V p.val q) (choices p) i) *
        ∏ i, (giantSignedPrimeVisitGhostFactor choices V ρ offset q i p *
          giantSignedPrimeAfterHalf choices ρ offset i p) *
          giantSignedPrimeBeforeHalf choices ρ offset i p := by
  unfold giantSignedPrimeChronologicalStatusProduct
  rw [← primeRunFactor_zero (choices p) V (giantSignedRowBirthAtom V p.val q)]
  simp_rw [primeRunFactor_succ (choices p) V (giantSignedRowBirthAtom V p.val q)]
  have hAfter : giantSignedPrimeAfterHalf choices ρ offset (Fin.last N) p = 1 := by
    simp [giantSignedPrimeAfterHalf, giantSignedPrimePendingAfter_last]
  have hBefore : giantSignedPrimeBeforeHalf choices ρ offset 0 p = 1 := by
    simp [giantSignedPrimeBeforeHalf, giantSignedPrimePendingBefore_first]
  exact join_visit_product
    (fun i => giantSignedPrimeVisitGhostFactor choices V ρ offset q i p)
    (fun i => giantSignedPrimeAfterHalf choices ρ offset i p)
    (fun i => giantSignedPrimeBeforeHalf choices ρ offset i p)
    (fun i => giantSignedPrimeVisitRunFactor V (giantSignedRowBirthAtom V p.val q) (choices p) i)
    hAfter hBefore

theorem giantSignedPrimeVisitRunFactor_product_of_view (V ν : ℝ) {S : Finset (Fin n)}
    (choice : GiantSignedResidueLifespanChoice S) {L : GiantSignedPrimeLifespanInterval S}
    (hview : giantSignedPrimeLifespanView S choice = some L) :
    (∏ i, giantSignedPrimeVisitRunFactor V ν choice i) =
      if L.ghostBirth = true then
        (((V⁻¹) ^ giantSignedActiveRunCount S : ℝ) : ℂ)
      else ((ν * (V⁻¹) ^ (giantSignedActiveRunCount S - 1) : ℝ) : ℂ) := by
  let runs := giantSignedActiveRunStarts S
  have hfilter : Finset.univ.filter (fun i : Fin n => i ∈ runs) = runs := by
    ext i
    simp
  change (∏ i, if i ∈ runs then
      if giantSignedPrimeFreshAt choice i then (ν : ℂ) else ((V⁻¹ : ℝ) : ℂ) else 1) = _
  rw [← Finset.prod_filter, hfilter]
  by_cases hBirth : L.ghostBirth = true
  · have hFresh (i : Fin n) : ¬giantSignedPrimeFreshAt choice i := by
      rw [giantSignedPrimeFreshAt, hview, Option.elim_some]
      rintro ⟨he, hi⟩
      exact (L.ghostBirth_iff.mp hBirth) (he.symm ▸ hi)
    simp only [hBirth, hFresh, ite_true, ite_false, Finset.prod_const, Complex.ofReal_pow]
    rfl
  · have hStart : L.start ∈ S := by
      by_contra hn
      exact hBirth (L.ghostBirth_iff.mpr hn)
    have hStartRun : L.start ∈ runs := by
      change L.start ∈ giantSignedActiveRunStarts S
      rw [giantSignedActiveRunStarts, Finset.mem_filter]
      refine ⟨hStart, ?_⟩
      rintro ⟨i, hi, he⟩
      have hli := (L.active_contained i hi).1
      change L.start.val ≤ i.val at hli
      omega
    have hFresh (i : Fin n) : giantSignedPrimeFreshAt choice i ↔ L.start = i := by
      rw [giantSignedPrimeFreshAt, hview, Option.elim_some]
      exact ⟨And.left, fun he => ⟨he, he ▸ hStart⟩⟩
    rw [← Finset.mul_prod_erase _ _ hStartRun]
    have hp : (∏ i ∈ runs.erase L.start, if giantSignedPrimeFreshAt choice i then
        (ν : ℂ) else ((V⁻¹ : ℝ) : ℂ)) = ∏ _i ∈ runs.erase L.start, ((V⁻¹ : ℝ) : ℂ) := by
      apply Finset.prod_congr rfl
      intro i hi
      exact ite_eq_right (fun h => (Finset.mem_erase.mp hi).1 ((hFresh i).mp h).symm)
    rw [hp, Finset.prod_const, Finset.card_erase_of_mem hStartRun]
    simp only [hBirth, ite_false, hFresh L.start, eq_self, ite_true,
      Complex.ofReal_mul, Complex.ofReal_pow]
    rfl

theorem giantSignedPrimeChronologicalStatusProduct_none {N : ℕ}
    {active : (p : P) → Finset (Fin (N + 1))}
    (choices : (p : P) → GiantSignedResidueLifespanChoice (active p)) (V ρ : ℝ)
    (offset : Fin (N + 1) → ℤ) (q : Fin (N + 1) → ℝ) (p : P)
    (hview : giantSignedPrimeLifespanView (active p) (choices p) = none) :
    giantSignedPrimeChronologicalStatusProduct choices V ρ offset q p = 1 := by
  have ha := giantSignedPrimeLifespanView_none_empty (active p) (choices p) hview
  rw [giantSignedPrimeChronologicalStatusProduct_eq_visits]
  have hr : giantSignedActiveRunStarts (active p) = ∅ := by
    rw [ha, giantSignedActiveRunStarts, Finset.filter_empty]
  simp only [giantSignedPrimeVisitRunFactor, hr, Finset.notMem_empty, ite_false,
    Finset.prod_const_one, giantSignedPrimeVisitGhostFactor, giantSignedGhostVisitPrimeFactor,
    giantSignedGhostVisitRetainedZero, giantSignedPrimeAfterHalf, giantSignedPrimeBeforeHalf,
    giantSignedPrimePendingBefore, giantSignedPrimePendingAfter, giantSignedPrimeGhostBirthAt,
    giantSignedPrimeGhostDeathAt, hview, Option.elim_none, false_and, mul_one]

end

end ArtinMatthews
