module

public import ArtinMatthews.GiantSignedActualFrameBoundary
public import ArtinMatthews.GiantSignedChronologicalMemoAccept
public import ArtinMatthews.GiantSignedGhostMemoRule
public import ArtinMatthews.GiantSignedEdgeMemoRule
public import ArtinMatthews.GiantSignedPrefixLocalTests


set_option backward.privateInPublic true
@[expose] public section

/-! A complete capped birth event is accepted by the chronological
memo rules on precisely its original trace. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

universe u
variable {S B I : Type u} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell n H : ℕ}
    (hPB : ∀ g p, p ∈ PB g → p.Prime)
    (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (q ρ θ : ℝ)
    (patterns : Fin n → Finset I) (C : Fin n → I → B → Finset (Fin k))
    (κ : Fin n → ℤ) (visitQ : Fin (n+1) → ℝ) (ζ : Fin n → ℝ)
    (K : (i : Fin n) → (a : I) → GiantTwoSidedPatternCoefficient PB (C i a) ell)
    (η : (i : Fin n) → (a : I) → (s : GiantSignedState PS PB (k+ell)) →
      GiantSignedRawEdgeMove PS PB ell (C i a) s.2.2 → ℂ)
    (v vmin mass : ℝ) (budget : ℕ) (BS W Δ : ℝ)
    (σ : Equiv.Perm (GiantSignedUniformBirthAddress B (k+ell) n H))

def giantSignedVisitMemoRule (i : Fin (n+1)) :
    GiantSignedTraceMemoRule (GiantSignedBirthMemo B (k+ell) n H)
      (giantSignedVisitTraceRow (PS := PS) (M := k+ell) ν V (visitQ i) ρ) :=
  giantSignedGhostMemoRule hPB ν (fun _ => ((visitQ i / ρ^2 : ℝ) : ℂ))
    (fun g => ((-(1-visitQ i) * V g / ρ : ℝ) : ℂ))
    (fun _ => ((-(1-visitQ i) / ρ : ℝ) : ℂ)) v mass Δ σ i

local notation "Rows" => giantSignedChronologicalTraceRows ν V q ρ θ n patterns C κ visitQ ζ K η
local notation "VisitRules" => giantSignedVisitMemoRule (PS := PS) hPB ν V ρ visitQ v mass Δ σ
local notation "EdgeRules" => fun i => giantSignedEdgeMemoRule hPB ν V (patterns i) (C i) (κ i) q ρ θ
  (ζ i) (K i) (η i) v vmin mass budget BS W Δ σ i

def giantSignedActualBirthMemoRules : GiantSignedTraceMemoRules (GiantSignedBirthMemo B (k+ell) n H) Rows :=
  giantSignedChronologicalMemoRules ν V q ρ θ n patterns C κ visitQ ζ K η VisitRules EdgeRules

theorem giantSignedActualBirthMemoRules_accept (s : GiantSignedState PS PB (k+ell))
    (t : GiantSignedCappedTrace H Rows s)
    (he : MarkedBirthPermutationEvent
      (giantSignedCappedTraceBirthValue H ν V q ρ θ n patterns C κ visitQ ζ K η s t) σ) :
    GiantSignedUniformBirthConditionalGate σ .initial (giantSignedInitialBirthMemo hPB s.2.1) ∧
    GiantSignedTraceMemoAccept Rows
      (giantSignedActualBirthMemoRules hPB ν V q ρ θ patterns C κ visitQ ζ K η v vmin mass budget BS W Δ σ)
      (giantSignedInitialBirthMemo hPB s.2.1) s t.val := by
  let z := giantSignedTraceChronology ν V q ρ θ n patterns C κ visitQ ζ K η s t.val
  let d := giantSignedChronologicalBirthData z.history
  have hH := giantSignedTraceChronology_batch_le ν V q ρ θ n patterns C κ visitQ ζ K η s t.val H t.property
  have he' : MarkedBirthPermutationEvent (giantSignedUniformBirthValue d H hH) σ := he
  let μG (i : Fin (n+1)) := giantSignedUniformBirthPrefixMemo d hH (giantSignedBirthOperationTime (.visit i))
  let μE (i : Fin n) := giantSignedUniformBirthPrefixMemo d hH (giantSignedBirthOperationTime (.edge i))
  let φ (i : Fin (n+1)) (b : B → ℕ) (born : ∀ g, Fin (b g) → PB g) : ℂ :=
    if GiantSignedVisitPrefixCondition hPB d hH σ i b born then 1 else 0
  let F (i : Fin n) (a : I) (target : MarkedPhysicalMarking PB (k+ell))
      (promoted : ∀ g, Finset (Fin (ell+(C i a g).card))) : ℂ :=
    if GiantSignedEdgePrefixCondition hPB d hH σ i target promoted then 1 else 0
  let ψ (i : Fin n) (a : I) (x : GiantSignedState PS PB (k+ell))
      (r : GiantSignedRawEdgeMove PS PB ell (C i a) x.2.2) := F i a r.bigTarget r.choice.2.1
  have hG (i : Fin (n+1)) (x : GiantSignedState PS PB (k+ell)) (r : GiantSignedGhostMemoryMoves x.2.2)
      (h : φ i (fun g => (r g).2.1) (fun g => (r g).2.2) ≠ 0) :
      GiantSignedVisitPrefixCondition hPB d hH σ i (fun g => (r g).2.1) (fun g => (r g).2.2) := by
    by_contra hn
    exact h (ite_eq_right hn)
  have hE (i : Fin n) (x : GiantSignedState PS PB (k+ell))
      (r : Σ a : patterns i, GiantSignedRawEdgeMove PS PB ell (C i a.val) x.2.2)
      (h : ψ i r.1.val x r.2 ≠ 0) :
      (EdgeRules i).accept (μE i) x r ∧ (EdgeRules i).update (μE i) x r = μG i.succ := by
    have ht : GiantSignedEdgePrefixCondition hPB d hH σ i r.2.bigTarget r.2.choice.2.1 := by
      by_contra hn
      exact h (ite_eq_right hn)
    have htime : giantSignedBirthOperationTime (.edge i) + 1 = giantSignedBirthOperationTime (.visit i.succ) := by
      simp only [giantSignedBirthOperationTime, Fin.val_succ]
      omega
    exact ⟨ht.1,ht.2.trans (congrArg (giantSignedUniformBirthPrefixMemo d hH) htime)⟩
  have htrace := giantSignedChronologicalMemoAccept_of_product_ne_zero ν V q ρ θ n patterns C κ visitQ ζ K η
    VisitRules EdgeRules μG μE ψ φ
    (fun i x r h => by
      obtain ⟨hb,hg,_⟩ := hG i x r h
      have hb' : GiantSignedGhostBatchFits H r := hb
      simpa only [giantSignedVisitMemoRule, giantSignedGhostMemoRule, dite_eq_left hb'] using hg)
    (fun i x r h => by
      obtain ⟨hb,_,hg⟩ := hG i.castSucc x r h
      have htime : giantSignedBirthOperationTime (.visit i.castSucc) + 1 = giantSignedBirthOperationTime (.edge i) := rfl
      unfold giantSignedVisitMemoRule giantSignedGhostMemoRule
      exact (dite_eq_left hb).trans (hg.trans (congrArg (giantSignedUniformBirthPrefixMemo d hH) htime)))
    hE s t.val
  have hprod := giantSignedTraceMultipliersProduct_birthData ν V q ρ θ n patterns C κ visitQ ζ K η s t.val F φ
  have hv (i : Fin (n+1)) : φ i (z.batch i) (d.born i) = 1 :=
    ite_eq_left (giantSignedVisitPrefixCondition_of_event hPB d hH σ he' i)
  have hh (i : Fin n) : F i (z.pattern i).val (d.target i) (d.promoted i) = 1 :=
    ite_eq_left (giantSignedEdgePrefixCondition_of_event hPB d hH σ he' i)
  have hprod' : (∏ i, φ i (z.batch i) (d.born i)) *
      (∏ i, F i (z.pattern i).val (d.target i) (d.promoted i)) = 1 := by simp only [hv, hh, Finset.prod_const_one, one_mul]
  have hA := htrace ((hprod.trans hprod').trans_ne one_ne_zero)
  have hi : d.initial = s.2.1 := congrArg (fun x : GiantSignedState PS PB (k+ell) => x.2.1) z.first
  have hInit : GiantSignedUniformBirthConditionalGate σ .initial (giantSignedInitialBirthMemo hPB s.2.1) ∧
      giantSignedInitialBirthMemo hPB s.2.1 = μG 0 :=
    hi ▸ giantSignedInitialBirthMemo_prefix hPB d hH σ he'
  exact ⟨hInit.1,hInit.2.symm ▸ hA⟩

end
end ArtinMatthews
