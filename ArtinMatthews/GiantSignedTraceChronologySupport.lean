module

public import ArtinMatthews.GiantSignedTraceChronology
public import ArtinMatthews.GiantSignedRawReplay


set_option backward.privateInPublic true
@[expose] public section

/-! A nonzero original trace has compatible chronological moves and an
empty terminal memory. Its coefficient is exactly the product of the
extracted ghost and edge coefficients. -/

namespace ArtinMatthews
open scoped BigOperators
noncomputable section

universe u
variable {S B I : Type u} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell : ℕ}

private theorem edgeChoice_transport_heq {t d e : B → ℕ} (h : d = e)
    (r : GiantSignedEdgeChoice t d) : HEq (h ▸ r : GiantSignedEdgeChoice t e) r := by
  subst e
  rfl

variable (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (q ρ θ : ℝ)
    (n : ℕ) (patterns : Fin n → Finset I) (C : Fin n → I → B → Finset (Fin k))
    (κ : Fin n → ℤ) (visitQ : Fin (n+1) → ℝ) (ζ : Fin n → ℝ)
    (K : (i : Fin n) → (a : I) → GiantTwoSidedPatternCoefficient PB (C i a) ell)
    (s : GiantSignedState PS PB (k+ell))

local notation "One" => fun _ _ _ _ => (1 : ℂ)
local notation "Rows" => giantSignedChronologicalTraceRows ν V q ρ θ n patterns C κ visitQ ζ K One

theorem giantSignedTraceChronology_support
    (t : GiantSignedTrace Rows s) (hnz : giantSignedTraceWeight giantSignedBoundary Rows s t ≠ 0) :
    let z := giantSignedTraceChronology ν V q ρ θ n patterns C κ visitQ ζ K One s t
    let h := z.history
    GiantSignedChronologicalCompatible κ h ∧
      giantSignedChronologicalGhostTarget h (Fin.last n) = giantSignedEmptyMemory PB ∧
      giantSignedTraceWeight giantSignedBoundary Rows s t =
        (∏ i, giantSignedChronologicalGhostCoefficient ν V visitQ ρ h i) *
          ∏ i, giantSignedChronologicalEdgeCoefficient ν V κ q ρ θ ζ (fun i => K i (z.pattern i).val) h i := by
  induction n generalizing s with
  | zero =>
    obtain ⟨r,u⟩ := t
    cases u
    let z := giantSignedTraceChronology ν V q ρ θ 0 patterns C κ visitQ ζ K One s ⟨r,PUnit.unit⟩
    let g := giantSignedVisitTraceRow (PS := PS) (M := k+ell) ν V (visitQ 0) ρ
    change g.coefficient s r * giantSignedBoundary (g.target s r) ≠ 0 at hnz
    have hb : (g.target s r).2.2 = giantSignedEmptyMemory PB := by
      by_contra h
      exact (mul_ne_zero_iff.mp hnz).2 (by rw [giantSignedBoundary, ite_eq_right h])
    have hr := giantSignedFixedGhostMove_of_move s.2.2 r
    refine ⟨(fun i => Fin.elim0 i), ?_, ?_⟩
    · change giantSignedGhostMemoryMoveTarget s.2.2
        (giantSignedFixedGhostMove s.2.2 (fun j => (r j).2.1) (fun j => (r j).1) (fun j => (r j).2.2)) = _
      rw [hr]
      exact hb
    · change g.coefficient s r * giantSignedBoundary (g.target s r) =
        (∏ i : Fin 1, giantSignedChronologicalGhostCoefficient ν V visitQ ρ z.history i) *
          ∏ i : Fin 0, giantSignedChronologicalEdgeCoefficient ν V κ q ρ θ ζ
            (fun i => K i (z.pattern i).val) z.history i
      rw [giantSignedBoundary, ite_eq_left hb, Fin.prod_univ_zero, Fin.prod_univ_one, mul_one, mul_one]
      exact (congrArg (giantSignedGhostMemoryMoveCoefficient ν
        (fun _ => ((visitQ 0/ρ^2 : ℝ) : ℂ)) (fun j => ((-(1-visitQ 0)*V j/ρ : ℝ) : ℂ))
        (fun _ => ((-(1-visitQ 0)/ρ : ℝ) : ℂ)) s.2.2) hr).symm
  | succ n ih =>
    let G := giantSignedVisitTraceRow (PS := PS) (M := k+ell) ν V (visitQ 0) ρ
    let E := giantSignedEdgeTraceRow (PS := PS) ν V (patterns 0) (C 0) (κ 0) q ρ θ (ζ 0) (K 0)
      (fun _ _ _ => 1)
    let rest := giantSignedChronologicalTraceRows (PS := PS) ν V q ρ θ n (fun i => patterns i.succ)
      (fun i => C i.succ) (fun i => κ i.succ) (fun i => visitQ i.succ) (fun i => ζ i.succ)
      (fun i => K i.succ) One
    obtain ⟨r,e,t⟩ := t
    let a := G.target s r
    let x := E.target a e
    let tail := giantSignedTraceChronology ν V q ρ θ n (fun i => patterns i.succ)
      (fun i => C i.succ) (fun i => κ i.succ) (fun i => visitQ i.succ) (fun i => ζ i.succ)
      (fun i => K i.succ) One x t
    let z := giantSignedTraceChronology ν V q ρ θ (n+1) patterns C κ visitQ ζ K One s ⟨r,e,t⟩
    let h := z.history
    let W := giantSignedTraceWeight giantSignedBoundary rest x t
    change G.coefficient s r * (E.coefficient a e * W) ≠ 0 at hnz
    have hE := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hnz).2).1
    have hW := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hnz).2).2
    have hTail := ih (fun i => patterns i.succ) (fun i => C i.succ) (fun i => κ i.succ)
      (fun i => visitQ i.succ) (fun i => ζ i.succ) (fun i => K i.succ) x t hW
    have hraw : GiantSignedRawEdgeCondition (κ 0) a e.2 := by
      by_contra hbad
      apply hE
      change giantSignedRawEdgeCoefficient ν V (κ 0) q ρ θ (ζ 0) (K 0 e.1.val) a e.2 * 1 = 0
      rw [giantSignedRawEdgeCoefficient, ite_eq_right hbad, zero_mul]
    have hm : giantSignedFixedGhostTarget s.2.2 (fun j => (r j).2.1) (fun j => (r j).1)
        (fun j => (r j).2.2) = a.2.2 :=
      congrArg (giantSignedGhostMemoryMoveTarget s.2.2) (giantSignedFixedGhostMove_of_move s.2.2 r)
    have hs : giantSignedChronologicalAfterVisitState h (0 : Fin (n+1)).castSucc = a :=
      Prod.ext rfl (Prod.ext rfl hm)
    have hx : h.state (0 : Fin (n+1)).succ = x := tail.first
    have hchoice : HEq (h.edge (0 : Fin (n+1))) e.2.choice :=
      edgeChoice_transport_heq (congrArg Sigma.fst hm).symm e.2.choice
    have he := giantSignedChronologicalRawMove_replay (κ 0) h 0 a e.2 hs hx rfl rfl rfl rfl rfl hchoice
    have hc0 := (giantSignedRawEdgeCondition_replay (κ 0) hs he).mpr hraw
    have htarget := (giantSignedRawEdgeTarget_replay (κ 0) hs he).trans hx.symm
    have hc : GiantSignedChronologicalCompatible κ h := by
      intro i
      refine Fin.cases ?_ (fun j => hTail.1 j) i
      exact ⟨hc0.1,hc0.2.1,hc0.2.2.1,
        congrArg (fun s : GiantSignedState PS PB (k+ell) => s.2.2) htarget.symm,
        hc0.2.2.2.1,hc0.2.2.2.2⟩
    refine ⟨hc,hTail.2.1,?_⟩
    let F (i : Fin (n+2)) := giantSignedChronologicalGhostCoefficient ν V visitQ ρ h i
    let J (i : Fin (n+1)) := giantSignedChronologicalEdgeCoefficient ν V κ q ρ θ ζ
      (fun i => K i (z.pattern i).val) h i
    let X := ∏ i : Fin (n+1), F i.succ
    let Y := ∏ i : Fin n, J i.succ
    have hF₀ : F 0 = G.coefficient s r :=
      congrArg (giantSignedGhostMemoryMoveCoefficient ν (fun _ => ((visitQ 0/ρ^2 : ℝ) : ℂ))
        (fun j => ((-(1-visitQ 0)*V j/ρ : ℝ) : ℂ)) (fun _ => ((-(1-visitQ 0)/ρ : ℝ) : ℂ)) s.2.2)
        (giantSignedFixedGhostMove_of_move s.2.2 r)
    have hJ₀ : J 0 = E.coefficient a e := by
      exact (giantSignedChronologicalRawMove_coefficient ν V κ q ρ θ ζ
        (fun i => K i (z.pattern i).val) h hc 0).symm.trans
          ((giantSignedRawEdgeCoefficient_replay ν V (κ 0) q ρ θ (ζ 0) (K 0 e.1.val) hs he).trans
            (mul_one _).symm)
    have hF : (∏ i, F i) = G.coefficient s r * X :=
      (Fin.prod_univ_succ F).trans (congrArg (fun b => b*X) hF₀)
    have hJ : (∏ i, J i) = E.coefficient a e * Y :=
      (Fin.prod_univ_succ J).trans (congrArg (fun b => b*Y) hJ₀)
    have hXY : W = X*Y := hTail.2.2
    change G.coefficient s r * (E.coefficient a e * W) = (∏ i, F i) * ∏ i, J i
    rw [hXY,hF,hJ]
    ac_rfl

end
end ArtinMatthews
