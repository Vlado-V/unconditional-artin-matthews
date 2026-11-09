module

public import ArtinMatthews.GiantSignedPackedChronology
public import ArtinMatthews.GiantSignedChronologicalPackedExt


set_option backward.privateInPublic true
@[expose] public section

/-! Decoding a replay returns the exact ordered chronological data,
including its original selected patterns and birth-batch lengths. -/

namespace ArtinMatthews
noncomputable section

private theorem dependent_cast_apply {X Y : Type*} {T : X → Type*} (F : ∀ x, T x → Y)
    {x y : X} (h : x = y) (t : T y) : F x (cast (congrArg T h.symm) t) = F y t := by
  subst y
  rfl

universe u
variable {S B I : Type u} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell : ℕ}

local notation "One" => fun _ _ _ _ => (1 : ℂ)

theorem giantSignedTraceOfChronology_decode (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (q ρ θ : ℝ)
    (n : ℕ) (patterns : Fin n → Finset I) (C : Fin n → I → B → Finset (Fin k))
    (κ : Fin n → ℤ) (visitQ : Fin (n+1) → ℝ) (ζ : Fin n → ℝ)
    (K : (i : Fin n) → (a : I) → GiantTwoSidedPatternCoefficient PB (C i a) ell)
    (p : (i : Fin n) → patterns i) (batch : Fin (n+1) → B → ℕ)
    (h : GiantSignedChronologicalChoices PS PB ell (fun i => C i (p i).val) batch)
    (hc : GiantSignedChronologicalCompatible κ h) :
    giantSignedTraceChronology_pack (giantSignedTraceChronology ν V q ρ θ n patterns C κ visitQ ζ K One
      (h.state 0) (giantSignedTraceOfChronology ν V q ρ θ n patterns C κ visitQ ζ K p batch h hc)) =
        ⟨p,batch,h⟩ := by
  induction n with
  | zero =>
    let p₀ : (i : Fin 0) → patterns i := fun i => Fin.elim0 i
    have hp : p = p₀ := funext fun i => Fin.elim0 i
    subst p
    let t := giantSignedTraceOfChronology ν V q ρ θ 0 patterns C κ visitQ ζ K p₀ batch h hc
    let z := giantSignedTraceChronology ν V q ρ θ 0 patterns C κ visitQ ζ K One (h.state 0) t
    change giantSignedTraceChronology_pack z = ⟨p₀,batch,h⟩
    have hb : z.batch = batch := by
      funext i
      rw [Fin.eq_zero i]
      rfl
    have hs : z.history.state = h.state := by
      funext i
      rw [Fin.eq_zero i]
      rfl
    apply Sigma.ext (show z.pattern = p₀ from rfl)
    apply heq_of_eq
    apply Sigma.ext hb
    refine giantSignedChronologicalChoices_heq z.history h hb hs ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · funext i
      exact Fin.elim0 i
    · funext i
      exact Fin.elim0 i
    · funext i
      exact Fin.elim0 i
    · funext i
      exact Fin.elim0 i
    · funext i
      exact Fin.elim0 i
    · intro i g
      rw [Fin.eq_zero i]
      rfl
    · exact fun i => Fin.elim0 i
  | succ n ih =>
    let r := giantSignedFixedGhostMove (h.state 0).2.2 (batch 0) (h.deleted 0) (h.born 0)
    let a := giantSignedChronologicalAfterVisitState h (0 : Fin (n+1)).castSucc
    let move := giantSignedChronologicalRawMove h (0 : Fin (n+1))
    let e : Σ p : patterns 0, GiantSignedRawEdgeMove PS PB ell (C 0 p.val) a.2.2 := ⟨p 0,move⟩
    let x := giantSignedRawEdgeTarget (κ 0) a move
    let y := h.state (0 : Fin (n+1)).succ
    have hxy : x = y := giantSignedChronologicalRawMove_target κ h hc 0
    let rest := giantSignedChronologicalTraceRows (PS := PS) ν V q ρ θ n (fun i => patterns i.succ)
      (fun i => C i.succ) (fun i => κ i.succ) (fun i => visitQ i.succ) (fun i => ζ i.succ)
      (fun i => K i.succ) One
    let decode (s : GiantSignedState PS PB (k+ell)) (t : GiantSignedTrace rest s) :=
      giantSignedTraceChronology_pack (giantSignedTraceChronology ν V q ρ θ n (fun i => patterns i.succ)
        (fun i => C i.succ) (fun i => κ i.succ) (fun i => visitQ i.succ) (fun i => ζ i.succ)
        (fun i => K i.succ) One s t)
    let t : GiantSignedTrace rest y := giantSignedTraceOfChronology ν V q ρ θ n (fun i => patterns i.succ)
      (fun i => C i.succ) (fun i => κ i.succ) (fun i => visitQ i.succ) (fun i => ζ i.succ)
      (fun i => K i.succ) (fun i => p i.succ) (fun i => batch i.succ) (giantSignedChronologicalTail h)
      (giantSignedChronologicalTail_compatible h κ hc)
    let tail : GiantSignedPackedChronology PS PB ell (fun i => patterns i.succ) (fun i => C i.succ) :=
      ⟨fun i => p i.succ,fun i => batch i.succ,giantSignedChronologicalTail h⟩
    have hTail : decode y t = tail :=
      ih (fun i => patterns i.succ) (fun i => C i.succ) (fun i => κ i.succ) (fun i => visitQ i.succ)
        (fun i => ζ i.succ) (fun i => K i.succ) (fun i => p i.succ) (fun i => batch i.succ)
        (giantSignedChronologicalTail h) (giantSignedChronologicalTail_compatible h κ hc)
    change giantSignedPackedChronology_prepend patterns C (h.state 0) r e
      (decode x (cast (congrArg (GiantSignedTrace rest) hxy.symm) t)) = ⟨p,batch,h⟩
    rw [dependent_cast_apply decode hxy t,hTail]
    exact giantSignedPackedChronology_prepend_tail patterns C p batch h

end
end ArtinMatthews
