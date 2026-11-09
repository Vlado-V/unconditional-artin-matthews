module

public import ArtinMatthews.GiantSignedTraceOfChronology


set_option backward.privateInPublic true
@[expose] public section

/-! Reading a compatible trace and replaying its ordered choices
recovers the same dependent trace of actual moves. -/

namespace ArtinMatthews
noncomputable section

universe u v

private theorem traceCons_heq {X : Type u} (r : GiantSignedTraceRow.{u,v} X)
    (rs : List (GiantSignedTraceRow.{u,v} X)) {x y : X} (hx : x = y)
    {a : r.Move x} {b : r.Move y} (hm : HEq a b)
    {s : GiantSignedTrace rs (r.target x a)} {t : GiantSignedTrace rs (r.target y b)} (ht : HEq s t) :
    HEq (⟨a,s⟩ : GiantSignedTrace (r::rs) x) (⟨b,t⟩ : GiantSignedTrace (r::rs) y) := by
  subst y
  have hm' := eq_of_heq hm
  subst b
  have ht' := eq_of_heq ht
  subst t
  rfl

private theorem transportChoice_heq {B : Type*} {t d e : B → ℕ} (h : d = e)
    (r : GiantSignedEdgeChoice t d) : HEq (h ▸ r : GiantSignedEdgeChoice t e) r := by
  subst e
  rfl

variable {S B I : Type u} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell : ℕ}

private theorem headEdge_heq (patterns : Finset I) (C : I → B → Finset (Fin k))
    {m m' : GiantSignedMemory PB} (hm : m = m') (a : patterns)
    (r : GiantSignedRawEdgeMove PS PB ell (C a.val) m) (r' : GiantSignedRawEdgeMove PS PB ell (C a.val) m')
    (hr : HEq r r') :
    HEq (⟨a,r⟩ : Σ a : patterns, GiantSignedRawEdgeMove PS PB ell (C a.val) m)
      (⟨a,r'⟩ : Σ a : patterns, GiantSignedRawEdgeMove PS PB ell (C a.val) m') := by
  subst m'
  cases eq_of_heq hr
  rfl

local notation "One" => fun _ _ _ _ => (1 : ℂ)

theorem giantSignedTraceChronology_replay (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (q ρ θ : ℝ)
    (n : ℕ) (patterns : Fin n → Finset I) (C : Fin n → I → B → Finset (Fin k))
    (κ : Fin n → ℤ) (visitQ : Fin (n+1) → ℝ) (ζ : Fin n → ℝ)
    (K : (i : Fin n) → (a : I) → GiantTwoSidedPatternCoefficient PB (C i a) ell)
    (s : GiantSignedState PS PB (k+ell))
    (t : GiantSignedTrace (giantSignedChronologicalTraceRows ν V q ρ θ n patterns C κ visitQ ζ K One) s)
    (hc : GiantSignedChronologicalCompatible κ
      (giantSignedTraceChronology ν V q ρ θ n patterns C κ visitQ ζ K One s t).history) :
    let z := giantSignedTraceChronology ν V q ρ θ n patterns C κ visitQ ζ K One s t
    HEq (giantSignedTraceOfChronology ν V q ρ θ n patterns C κ visitQ ζ K z.pattern z.batch z.history hc) t := by
  induction n generalizing s with
  | zero =>
    obtain ⟨r,u₀⟩ := t
    cases u₀
    let G := giantSignedVisitTraceRow (PS := PS) (M := k+ell) ν V (visitQ 0) ρ
    let r' := giantSignedFixedGhostMove s.2.2 (fun g => (r g).2.1) (fun g => (r g).1) (fun g => (r g).2.2)
    have hr : r' = r := giantSignedFixedGhostMove_of_move s.2.2 r
    exact traceCons_heq G [] (x := s) (y := s) rfl (heq_of_eq hr) (s := PUnit.unit) (t := PUnit.unit) HEq.rfl
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
    let r' := giantSignedFixedGhostMove s.2.2 (z.batch 0) (h.deleted 0) (h.born 0)
    have hr : r' = r := giantSignedFixedGhostMove_of_move s.2.2 r
    let a' := giantSignedChronologicalAfterVisitState h (0 : Fin (n+1)).castSucc
    have hm : a'.2.2 = a.2.2 := congrArg (giantSignedGhostMemoryMoveTarget s.2.2) hr
    have hs : a' = a := Prod.ext rfl (Prod.ext rfl hm)
    have ht : h.state (0 : Fin (n+1)).succ = x := tail.first
    have hchoice : HEq (h.edge (0 : Fin (n+1))) e.2.choice :=
      transportChoice_heq (congrArg Sigma.fst hm).symm e.2.choice
    let move := giantSignedChronologicalRawMove h (0 : Fin (n+1))
    have hmove : HEq move e.2 :=
      giantSignedChronologicalRawMove_replay (κ 0) h 0 a e.2 hs ht rfl rfl rfl rfl rfl hchoice
    let e' : E.Move a' := ⟨z.pattern 0,move⟩
    have he : HEq e' e := headEdge_heq (patterns 0) (C 0) hm e.1 move e.2 hmove
    let replay := giantSignedTraceOfChronology ν V q ρ θ n (fun i => patterns i.succ)
      (fun i => C i.succ) (fun i => κ i.succ) (fun i => visitQ i.succ) (fun i => ζ i.succ)
      (fun i => K i.succ) (fun i => z.pattern i.succ) (fun i => z.batch i.succ)
      (giantSignedChronologicalTail h) (giantSignedChronologicalTail_compatible h κ hc)
    have hReplay : HEq replay t :=
      ih (fun i => patterns i.succ) (fun i => C i.succ) (fun i => κ i.succ) (fun i => visitQ i.succ)
        (fun i => ζ i.succ) (fun i => K i.succ) x t (giantSignedChronologicalTail_compatible h κ hc)
    have hnext : E.target a' e' = h.state (0 : Fin (n+1)).succ :=
      giantSignedChronologicalRawMove_target κ h hc 0
    let t' : GiantSignedTrace rest (E.target a' e') := cast (congrArg (GiantSignedTrace rest) hnext.symm) replay
    have hTail : HEq t' t := (cast_heq _ _).trans hReplay
    have hCons := traceCons_heq E rest hs he hTail
    exact traceCons_heq G (E::rest) (x := s) (y := s) rfl (heq_of_eq hr) hCons

end
end ArtinMatthews
