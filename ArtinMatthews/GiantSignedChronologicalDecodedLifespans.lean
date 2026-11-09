module

public import ArtinMatthews.GiantSignedChronologicalEdgeMatch
public import ArtinMatthews.GiantSignedChronologicalLifespanCoefficient
public import ArtinMatthews.GiantSignedChronologicalSourceCompatibility
public import ArtinMatthews.GiantSignedLifespanPathSlots
public import ArtinMatthews.GiantSignedJoinedBigLifespanSupport


set_option backward.privateInPublic true
@[expose] public section

/-! A birth-distinct admissible chronology determines a supported
grouped lifespan choice with the original ordered local coefficients. -/

namespace ArtinMatthews
noncomputable section

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell n : ℕ}
    {C : Fin n → B → Finset (Fin k)} {batch : Fin (n+1) → B → ℕ}
    (h : GiantSignedChronologicalChoices PS PB ell C batch) (κ : Fin n → ℤ)
    (q : Fin (n+1) → ℝ)

local notation "Labels" => giantSignedChronologicalJoinedLabels h
local notation "Offset" => giantSignedChronologicalJoinedOffset h κ
local notation "Bands" => Sum.elim PS PB

structure GiantSignedChronologicalDecodedLifespans where
  choice : GiantSignedJoinedBigLifespanChoice Labels
  supported : GiantSignedJoinedBigLifespanSupported Labels Offset q choice
  coefficientData : GiantSignedChronologicalLifespanCoefficientData choice h Offset

def giantSignedChronologicalDecodeLifespans
    (ha : GiantSignedChronologicalAdmissible κ h)
    (hd : GiantSignedBirthDistinct (giantSignedChronologicalBirthData h))
    (hP : ∀ (g : S ⊕ B) (p : ℕ), p ∈ Bands g → p.Prime)
    (hdis : Pairwise (fun i j : S ⊕ B => Disjoint (Bands i) (Bands j)))
    (hκ : ∀ i, 0 < (κ i).natAbs) (hsize : ∀ i g p, p ∈ Bands g → (κ i).natAbs < p)
    (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1)
    (hb : ∀ g (p : PB g), giantSignedPrimeResidueBaseline p.val q ≠ 0) :
    GiantSignedChronologicalDecodedLifespans h κ q := by
  let A (g : B) (p : PB g) := giantSignedActualActiveVisits Labels p.val
  have hA (g : B) (p : PB g) (i : Fin (n+1)) : i ∈ A g p ↔ GiantSignedChronologicalActive h i g p :=
    giantSignedActiveVisits_iff_group_slot hdis Labels i (Sum.inr g) p
  have hBig : Pairwise (fun g g' : B => Disjoint (PB g) (PB g')) :=
    fun _ _ hne => hdis (fun he => hne (Sum.inr.inj he))
  let matched (g : B) (p : PB g) := giantSignedChronologicalPrimeMatch h κ q g p (A g p)
    ha hd hBig (hA g p) (hP (Sum.inr g) p.val p.property).pos hq0 hq1 (hb g p)
  let c : GiantSignedJoinedBigLifespanChoice Labels := fun g p => (matched g p).choice
  have hw : GiantSignedJoinedBigLifespanSupported Labels Offset q c := by
    rw [giantSignedChronologicalJoinedOffset_eq]
    exact fun g p => (matched g p).supported
  let mark (v : Fin (n+1)) := giantSignedChronologicalMarking_distinct h κ ha hd v
  have hs (i : Fin n) (g : B) :
      Function.Injective (giantSignedPatternFreeLabels (C i) (giantSignedChronologicalBigSource h i) g) :=
    giantSignedPatternFreeLabels_injective (C i) _
      (fun g => (mark i.castSucc g).comp (h.sourceBigPermutation i g).injective) g
  have ht (i : Fin n) (g : B) :
      Function.Injective (giantSignedPatternFreeLabels (C i) (giantSignedChronologicalBigTarget h i) g) :=
    giantSignedPatternFreeLabels_injective (C i) _
      (fun g => (mark i.succ g).comp (h.targetBigPermutation i g).injective) g
  have hStatic := giantSignedChronologicalJoinedStaticLabels_of_birthDistinct h κ ha hd
  have hCompatible := giantSignedChronologicalJoinedActiveCompatible h κ ha hd
    (fun s g => hdis (show (Sum.inl s : S ⊕ B) ≠ Sum.inr g from Sum.inl_ne_inr))
  have hTarget (i : Fin n) (g : B) (p : PB g) :
      (∃ j, giantSignedPatternFreeLabels (C i) (giantSignedChronologicalBigTarget h i) g j = p) ↔
        i.succ ∈ A g p ∧ i.castSucc ∉ A g p :=
    (giantSignedLifespanPath_free_slots hP hdis hκ hsize hStatic hCompatible i (Sum.inr g) p).2
  let data : GiantSignedChronologicalLifespanCoefficientData c h (giantSignedChronologicalOffset κ h) :=
    { before := giantSignedChronologicalBeforeMemoryMatch h κ matched ha hd
      after := giantSignedChronologicalAfterMemoryMatch h κ matched ha hd
      initialInjective := mark 0
      initialRange := fun g p => hA g p 0
      targetInjective := ht
      targetRange := hTarget
      ghostMatch := giantSignedChronologicalGhostMatch_of_prime h κ matched hd
      edgeMatch := fun i => giantSignedChronologicalEdgeMatch_of_prime h κ matched ha hd i hA (hs i) (ht i) }
  refine ⟨c,hw,?_⟩
  rw [giantSignedChronologicalJoinedOffset_eq]
  exact data

end
end ArtinMatthews
