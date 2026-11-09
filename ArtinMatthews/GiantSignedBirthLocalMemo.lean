module

public import ArtinMatthews.GiantSignedBirthConditionalMass
public import ArtinMatthews.GiantSignedBirthPrefixMemo
public import ArtinMatthews.GiantTwoSidedResidueInitialMass
public import ArtinMatthews.GiantSignedMemoryState


set_option backward.privateInPublic true
@[expose] public section

/-! The initial and visit gates on the actual independent fresh draws.
Current addresses are empty in every genuine prefix memo. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {B : Type*} [Fintype B] {PB : B → Finset ℕ} {M n H : ℕ}

abbrev GiantSignedBirthMemo (B : Type*) (M n H : ℕ) :=
  GiantSignedUniformBirthAddress B M n H → Option Nat.Primes

def giantSignedBirthClearCurrent (o : GiantSignedBirthOperation n) (old : GiantSignedBirthMemo B M n H) :
    GiantSignedBirthMemo B M n H :=
  fun a => if giantSignedUniformBirthOperation M n H a = o then none else old a

theorem giantSignedBirthClearCurrent_none (o : GiantSignedBirthOperation n)
    (old : GiantSignedBirthMemo B M n H) (a : GiantSignedUniformBirthAddress B M n H)
    (ha : giantSignedUniformBirthOperation M n H a = o) :
    giantSignedBirthClearCurrent o old a = none :=
  ite_eq_left ha

theorem giantSignedBirthClearCurrent_prefix {k ell : ℕ} {C : Fin n → B → Finset (Fin k)}
    {b : Fin (n+1) → B → ℕ} (d : GiantSignedBirthData PB ell C b) (hH : ∀ i g, b i g ≤ H)
    (o : GiantSignedBirthOperation n) :
    giantSignedBirthClearCurrent o (giantSignedUniformBirthPrefixMemo d hH (giantSignedBirthOperationTime o)) =
      giantSignedUniformBirthPrefixMemo d hH (giantSignedBirthOperationTime o) := by
  funext a
  by_cases ha : giantSignedUniformBirthOperation (k+ell) n H a = o
  · exact (giantSignedBirthClearCurrent_none o _ a ha).trans
      (giantSignedUniformBirthPrefixMemo_current_none d hH o a ha).symm
  · exact ite_eq_right ha

def giantSignedInitialBirthMemo (hPB : ∀ g p, p ∈ PB g → p.Prime)
    (a : MarkedPhysicalMarking PB M) : GiantSignedBirthMemo B M n H :=
  giantSignedUniformBirthConditionalValues hPB giantSignedInitialBirthDraw (fun _ => none)
    (fun z => a z.1 z.2)

def giantSignedVisitBirthMemo (hPB : ∀ g p, p ∈ PB g → p.Prime)
    (i : Fin (n+1)) (b : B → ℕ) (hb : ∀ g, b g ≤ H) (born : ∀ g, Fin (b g) → PB g)
    (old : GiantSignedBirthMemo B M n H) : GiantSignedBirthMemo B M n H :=
  giantSignedUniformBirthConditionalValues hPB (giantSignedVisitBirthDraw i b hb)
    (giantSignedBirthClearCurrent (.visit i) old) (fun z => born z.1 z.2)

variable (hPB : ∀ g p, p ∈ PB g → p.Prime)
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p)
    {Δ mass : ℝ} (hΔ : 0 ≤ Δ) (hmass : 1 ≤ mass)
    (hatom : ∀ g p, ν g p ≤ Δ) (hMass : ∀ g, (∑ p : PB g, ν g p) ≤ mass)
    (σ : Equiv.Perm (GiantSignedUniformBirthAddress B M n H))

include hν hΔ hmass hatom hMass in
theorem giantSignedInitialBirthMemo_mass_le :
    (∑ a : MarkedPhysicalMarking PB M,
      if GiantSignedUniformBirthConditionalGate σ .initial (giantSignedInitialBirthMemo hPB a)
      then giantSignedActiveMass ν a else 0) ≤
      Δ^(giantSignedUniformBirthStageNonpivots σ .initial).card * mass^(Fintype.card B*M) := by
  let e : (Σ _ : B, Fin M) ↪ GiantSignedUniformBirthAddress B M n H := giantSignedInitialBirthDraw
  let E := Equiv.piCurry (fun g (_ : Fin M) => PB g)
  let F (a : MarkedPhysicalMarking PB M) :=
    if GiantSignedUniformBirthConditionalGate σ .initial (giantSignedInitialBirthMemo hPB a)
    then giantSignedActiveMass ν a else 0
  have h := giantSignedUniformBirthConditional_mass hPB ν hν hΔ hmass hatom hMass σ .initial e
    (fun _ => none) (fun _ _ => rfl)
  change (∑ a, F a) ≤ _
  rw [← E.sum_comp F]
  refine (le_of_eq ?_).trans (h.trans_eq ?_)
  · refine Finset.sum_congr (congrArg
      (fun ft : Fintype ((x : Σ _ : B, Fin M) → PB x.1) => @Finset.univ _ ft)
      (Subsingleton.elim _ _)) ?_
    intro t _
    have ht : (fun z : Σ _ : B, Fin M => (E t) z.1 z.2) = t := by
      funext z
      cases z
      rfl
    have hterm :
        F (E t) = if GiantSignedUniformBirthConditionalGate σ .initial
          (giantSignedUniformBirthConditionalValues hPB e (fun _ => none) t)
          then ∏ g, ∏ j, ν g (t ⟨g,j⟩) else 0 := by
      unfold F giantSignedInitialBirthMemo
      rw [ht] <;> rfl
    change F (E t) = (if GiantSignedUniformBirthConditionalGate σ .initial
      (giantSignedUniformBirthConditionalValues hPB e (fun _ => none) t)
      then ∏ a : Σ _ : B, Fin M, ν a.1 (t a) else 0)
    rw [Fintype.prod_sigma]
    exact hterm
  · have hc : Fintype.card (Σ _ : B, Fin M) = Fintype.card B * M := by
      simp [Fintype.card_sigma]
    rw [hc]

include hν hΔ hmass hatom hMass in
theorem giantSignedVisitBirthMemo_mass_le (i : Fin (n+1)) (b : B → ℕ) (hb : ∀ g, b g ≤ H)
    (old : GiantSignedBirthMemo B M n H) :
    (∑ born : ∀ g, Fin (b g) → PB g,
      if GiantSignedUniformBirthConditionalGate σ (.visit i) (giantSignedVisitBirthMemo hPB i b hb born old)
      then ∏ g, ∏ j, ν g (born g j) else 0) ≤
      Δ^(giantSignedUniformBirthStageNonpivots σ (.visit i)).card * mass^(∑ g, b g) := by
  let e := giantSignedVisitBirthDraw (M := M) i b hb
  let E := Equiv.piCurry (fun g (_ : Fin (b g)) => PB g)
  let F (born : ∀ g, Fin (b g) → PB g) :=
    if GiantSignedUniformBirthConditionalGate σ (.visit i) (giantSignedVisitBirthMemo hPB i b hb born old)
    then ∏ g, ∏ j, ν g (born g j) else 0
  have h := giantSignedUniformBirthConditional_mass hPB ν hν hΔ hmass hatom hMass σ (.visit i) e
    (giantSignedBirthClearCurrent (.visit i) old) (giantSignedBirthClearCurrent_none (.visit i) old)
  change (∑ born, F born) ≤ _
  rw [← E.sum_comp F]
  refine (le_of_eq ?_).trans (h.trans_eq ?_)
  · refine Finset.sum_congr (congrArg
      (fun ft : Fintype ((x : Σ g : B, Fin (b g)) → PB x.1) => @Finset.univ _ ft)
      (Subsingleton.elim _ _)) ?_
    intro t _
    have ht : (fun z : Σ g : B, Fin (b g) => (E t) z.1 z.2) = t := by
      funext z
      cases z
      rfl
    have hterm :
        F (E t) = if GiantSignedUniformBirthConditionalGate σ (.visit i)
          (giantSignedUniformBirthConditionalValues hPB e (giantSignedBirthClearCurrent (.visit i) old) t)
          then ∏ g, ∏ j, ν g (t ⟨g,j⟩) else 0 := by
      unfold F giantSignedVisitBirthMemo
      rw [ht] <;> rfl
    change F (E t) = (if GiantSignedUniformBirthConditionalGate σ (.visit i)
      (giantSignedUniformBirthConditionalValues hPB e (giantSignedBirthClearCurrent (.visit i) old) t)
      then ∏ a : Σ g : B, Fin (b g), ν a.1 (t a) else 0)
    rw [Fintype.prod_sigma]
    exact hterm
  · simp only [Fintype.card_sigma, Fintype.card_fin]

include hν hΔ hmass hatom hMass in
theorem giantSignedInitialBirthBoundary_mass_le {S : Type*} [Fintype S] [DecidableEq S]
    (PS : S → Finset ℕ) [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
    (hPS : ∀ j p, p ∈ PS j → p.Prime) (hdis : Pairwise (fun i j => Disjoint (PS i) (PS j)))
    (hVS : ∀ j, 0 < bandReciprocalMass (PS j)) :
    (∑ _s : GiantTwoSidedResidueState PS M, ∑ a : MarkedPhysicalMarking PB M,
      if GiantSignedUniformBirthConditionalGate σ .initial (giantSignedInitialBirthMemo hPB a)
      then giantTwoSidedResidueHaarStateMass PS M * giantSignedActiveMass ν a else 0) ≤
      Δ^(giantSignedUniformBirthStageNonpivots σ .initial).card * mass^(Fintype.card B*M) := by
  let m := giantTwoSidedResidueHaarStateMass PS M
  let F (a : MarkedPhysicalMarking PB M) :=
    if GiantSignedUniformBirthConditionalGate σ .initial (giantSignedInitialBirthMemo hPB a)
    then giantSignedActiveMass ν a else 0
  have he (a : MarkedPhysicalMarking PB M) :
      (if GiantSignedUniformBirthConditionalGate σ .initial (giantSignedInitialBirthMemo hPB a)
        then m * giantSignedActiveMass ν a else 0) = m * F a := by
    unfold F
    split_ifs <;> simp only [mul_zero]
  calc
    _ = (∑ _s : GiantTwoSidedResidueState PS M, m) * ∑ a, F a := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro _ _
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun a _ => he a)
    _ ≤ ∑ a, F a :=
      mul_le_of_le_one_left
        (Finset.sum_nonneg (fun a _ => by
          unfold F
          split_ifs
          · exact Finset.prod_nonneg (fun g _ => Finset.prod_nonneg (fun i _ => hν g (a g i)))
          · exact le_rfl))
        (giantTwoSidedResidue_initialMass_le_one PS hPS hdis hVS M)
    _ ≤ _ := giantSignedInitialBirthMemo_mass_le hPB ν hν hΔ hmass hatom hMass σ

end
end ArtinMatthews
