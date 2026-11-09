module

public import ArtinMatthews.GiantSignedBirthTrace
public import ArtinMatthews.GiantSignedTraceChronology


set_option backward.privateInPublic true
@[expose] public section

/-! A capped trace records all its performed births. The local phase
product can be read either on the moves or on the extracted chronology. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

universe u
variable {S B I : Type u} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell : ℕ}
    (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (q ρ θ : ℝ)
    (n : ℕ) (patterns : Fin n → Finset I) (C : Fin n → I → B → Finset (Fin k))
    (κ : Fin n → ℤ) (visitQ : Fin (n+1) → ℝ) (ζ : Fin n → ℝ)
    (K : (i : Fin n) → (v : I) → GiantTwoSidedPatternCoefficient PB (C i v) ell)
    (η : (i : Fin n) → (v : I) → (s : GiantSignedState PS PB (k+ell)) →
      GiantSignedRawEdgeMove PS PB ell (C i v) s.2.2 → ℂ)
    (s : GiantSignedState PS PB (k+ell))
    (t : GiantSignedTrace (giantSignedChronologicalTraceRows ν V q ρ θ n patterns C κ visitQ ζ K η) s)

private theorem giantSignedEdgeChoice_transport_promotions {d e : B → ℕ} {T : B → ℕ}
    (h : d = e) (r : GiantSignedEdgeChoice T d) :
    (h ▸ r : GiantSignedEdgeChoice T e).2.1 = r.2.1 := by
  subst e
  rfl

theorem giantSignedTraceChronology_batch_le (H : ℕ)
    (ht : GiantSignedTraceWithin (fun x => (∑ g, x.2.2.1 g) ≤ H)
      (giantSignedChronologicalTraceRows ν V q ρ θ n patterns C κ visitQ ζ K η) s t) :
    ∀ i g, (giantSignedTraceChronology ν V q ρ θ n patterns C κ visitQ ζ K η s t).batch i g ≤ H := by
  induction n generalizing s with
  | zero =>
      obtain ⟨r,_⟩ := t
      have hpost : (∑ g, (giantSignedGhostMemoryMoveTarget s.2.2 r).1 g) ≤ H := ht.2.1
      intro i g
      change (r g).2.1 ≤ H
      exact (Nat.le_add_left _ _).trans
        ((Finset.single_le_sum (f := fun j => (giantSignedGhostMemoryMoveTarget s.2.2 r).1 j)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ g)).trans hpost)
  | succ n ih =>
      obtain ⟨r,e,t⟩ := t
      have hpost : (∑ g, (giantSignedGhostMemoryMoveTarget s.2.2 r).1 g) ≤ H := ht.2.1
      intro i g
      refine Fin.cases ?_ (fun j => ?_) i
      · change (r g).2.1 ≤ H
        exact (Nat.le_add_left _ _).trans
          ((Finset.single_le_sum (f := fun j => (giantSignedGhostMemoryMoveTarget s.2.2 r).1 j)
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ g)).trans hpost)
      · exact ih (fun i => patterns i.succ) (fun i => C i.succ) (fun i => κ i.succ)
          (fun i => visitQ i.succ) (fun i => ζ i.succ) (fun i => K i.succ) (fun i => η i.succ)
          _ t ht.2.2.2.2 j g

theorem giantSignedTraceMultipliersProduct_birthData
    (edge : (i : Fin n) → (v : I) → MarkedPhysicalMarking PB (k+ell) →
      ((g : B) → Finset (Fin (ell+(C i v g).card))) → ℂ)
    (visit : Fin (n+1) → GiantSignedGhostBirthMultiplier PB) :
    let rows := giantSignedChronologicalTraceRows ν V q ρ θ n patterns C κ visitQ ζ K η
    let φ := giantSignedChronologicalTraceMultipliers ν V q ρ θ n patterns C κ visitQ ζ K η
      (fun i v _ r => edge i v r.bigTarget r.choice.2.1) visit
    let z := giantSignedTraceChronology ν V q ρ θ n patterns C κ visitQ ζ K η s t
    let d := giantSignedChronologicalBirthData z.history
    giantSignedTraceMultipliersProduct rows φ s t =
      (∏ i, visit i (z.batch i) (d.born i)) *
        ∏ i, edge i (z.pattern i).val (d.target i) (d.promoted i) := by
  induction n generalizing s with
  | zero =>
      obtain ⟨r,_⟩ := t
      simp only [giantSignedChronologicalTraceRows, giantSignedChronologicalTraceMultipliers,
        giantSignedTraceMultipliersProduct, giantSignedTraceChronology, giantSignedChronologicalBirthData,
        Fin.prod_univ_zero, mul_one]
      change visit 0 (fun g => (r g).2.1) (fun g => (r g).2.2) =
        ∏ i : Fin 1, visit i (fun g => (r g).2.1) (fun g => (r g).2.2)
      exact (Fin.prod_univ_one (fun i : Fin 1 => visit i
        (fun g => (r g).2.1) (fun g => (r g).2.2))).symm
  | succ n ih =>
      let G := giantSignedVisitTraceRow (PS := PS) (M := k+ell) ν V (visitQ 0) ρ
      let E := giantSignedEdgeTraceRow ν V (patterns 0) (C 0) (κ 0) q ρ θ (ζ 0) (K 0) (η 0)
      obtain ⟨r,e,t⟩ := t
      let after := G.target s r
      let next := E.target after e
      let tail := giantSignedTraceChronology ν V q ρ θ n (fun i => patterns i.succ)
        (fun i => C i.succ) (fun i => κ i.succ) (fun i => visitQ i.succ)
        (fun i => ζ i.succ) (fun i => K i.succ) (fun i => η i.succ) next t
      let all := giantSignedTraceChronology ν V q ρ θ (n+1) patterns C κ visitQ ζ K η s ⟨r,e,t⟩
      let d := giantSignedChronologicalBirthData all.history
      have hnext : all.history.state (Fin.succ 0) = next := tail.first
      have htarget : d.target 0 = e.2.bigTarget := by
        change (fun g i => (all.history.state (Fin.succ 0)).2.1 g (e.2.targetBigPermutation g i)) = _
        rw [hnext]
        exact (giantSignedGroupedTuplePermutation e.2.targetBigPermutation).apply_symm_apply _
      have hp : d.promoted 0 = e.2.choice.2.1 := by
        let hd := congrArg (fun m : GiantSignedGhostMemoryMoves s.2.2 =>
          (giantSignedGhostMemoryMoveTarget s.2.2 m).1)
          (giantSignedFixedGhostMove_of_move s.2.2 r)
        exact giantSignedEdgeChoice_transport_promotions hd.symm e.2.choice
      have ht := ih (fun i => patterns i.succ) (fun i => C i.succ) (fun i => κ i.succ)
        (fun i => visitQ i.succ) (fun i => ζ i.succ) (fun i => K i.succ) (fun i => η i.succ)
        next t (fun i => edge i.succ) (fun i => visit i.succ)
      let a := visit 0 (fun g => (r g).2.1) (fun g => (r g).2.2)
      let b := edge 0 e.1.val e.2.bigTarget e.2.choice.2.1
      let F (i : Fin (n+2)) := visit i (all.batch i) (d.born i)
      let J (i : Fin (n+1)) := edge i (all.pattern i).val (d.target i) (d.promoted i)
      let X := ∏ i : Fin (n+1), F i.succ
      let Y := ∏ i : Fin n, J i.succ
      have hF : (∏ i, F i) = a * X := Fin.prod_univ_succ F
      have hb : J 0 = b := congrArg₂ (edge 0 e.1.val) htarget hp
      have hJ : (∏ i, J i) = b * Y :=
        (Fin.prod_univ_succ J).trans (congrArg (fun z => z * Y) hb)
      calc
        _ = a * (b * (X * Y)) := congrArg (fun z => a * (b*z)) ht
        _ = (a * X) * (b * Y) := by ac_rfl
        _ = _ := congrArg₂ (· * ·) hF.symm hJ.symm

end
end ArtinMatthews
