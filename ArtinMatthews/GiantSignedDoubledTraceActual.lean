module

public import ArtinMatthews.GiantSignedDoubledTraceWeight
public import ArtinMatthews.GiantSignedTraceActual


set_option backward.privateInPublic true
@[expose] public section

/-! The actual doubled trace is absolutely convergent and sums to the
original doubled positive word with the literal raw edge phases. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

universe u
variable {S B I : Type u} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell : ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
    [∀ g, ∀ p : PB g, NeZero p.val]
    (hPS : ∀ j p, p ∈ PS j → p.Prime) (hPB : ∀ j p, p ∈ PB j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (PS i) (PS j)))
    (hVS : ∀ j, 0 < bandReciprocalMass (PS j)) (hVB : ∀ g, 0 < bandReciprocalMass (PB g))
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (V : B → ℝ)
    {vmin massMax q ρ BS W : ℝ} (hvmin : 0 < vmin) (hV : ∀ g, vmin ≤ V g)
    (hMass : ∀ g, (∑ p : PB g, ν g p) ≤ massMax)
    (hq : 0 < q) (hq1 : q ≤ 1) (hBS : 0 ≤ BS)
    (hbudget : ∀ j (z : ℕ), (bandReciprocalMass (PS j))⁻¹ ^ ell *
      ((z : ℝ) + (ell : ℝ)) ^ ell * q ^ ((z : ℝ) / 2) ≤ BS)
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hW : 0 ≤ W) (budget : ℕ)

include hPS hPB hdis hVS hVB hν hvmin hV hMass hq hq1 hBS hbudget hρ hρ1 hW budget in
theorem giantSignedDoubledTraceRows_absolute (θ : ℝ) (n : ℕ)
    (patterns : Fin n → Finset I) (C : Fin n → I → B → Finset (Fin k))
    (hC : ∀ i v, v ∈ patterns i → ∀ g, (C i v g).card ≤ budget)
    (κ : Fin n → ℤ) (visitQ : Fin (n+1) → ℝ) (ζ : Fin n → ℝ)
    (K : (i : Fin n) → (v : I) → GiantTwoSidedPatternCoefficient PB (C i v) ell)
    (hK : ∀ i v, v ∈ patterns i → ∀ a b aux, ‖K i v a b aux‖ ≤ W)
    (η : (i : Fin n) → (v : I) → (s : GiantSignedState PS PB (k+ell)) →
      GiantSignedRawEdgeMove PS PB ell (C i v) s.2.2 → ℂ)
    (hη : ∀ i v, v ∈ patterns i → ∀ s r, ‖η i v s r‖ ≤ 1) :
    ∀ r ∈ giantSignedDoubledTraceRows ν V q ρ θ n patterns C κ visitQ ζ K η,
      GiantSignedTraceRowAbsolute (fun s : GiantSignedState PS PB (k+ell) => ∑ g, s.2.2.1 g) r := by
  induction n with
  | zero =>
      intro r hr
      change r ∈ [giantSignedDoubledVisitTraceRow ν V (visitQ 0) ρ] at hr
      rcases List.mem_singleton.mp hr with rfl
      exact giantSignedGhostTraceRow_absolute ν hν _ _ _
  | succ n ih =>
      intro r hr
      simp only [giantSignedDoubledTraceRows, List.mem_cons] at hr
      rcases hr with rfl | rfl | hr
      · exact giantSignedGhostTraceRow_absolute ν hν _ _ _
      · exact giantSignedEdgeTraceRow_absolute hPS hPB hdis hVS hVB ν hν V
          hvmin hV hMass hq hq1 hBS hbudget hρ hρ1 hW budget (patterns 0) (C 0) (hC 0)
          (κ 0) θ (ζ 0) (K 0) (hK 0)
          (fun v => giantSignedRawEdgeAbsoluteMultiplier ν V (κ 0) q ρ θ (ζ 0) (K 0 v) (η 0 v))
          (fun v hv s r => giantSignedRawEdgeAbsoluteMultiplier_norm_le ν V (κ 0) q ρ θ (ζ 0)
            (K 0 v) (η 0 v) s r (hη 0 v hv s r))
      · exact ih (fun i => patterns i.succ) (fun i => C i.succ) (fun i => hC i.succ)
          (fun i => κ i.succ) (fun i => visitQ i.succ) (fun i => ζ i.succ)
          (fun i => K i.succ) (fun i => hK i.succ) (fun i => η i.succ) (fun i => hη i.succ) r hr

include hPS hPB hdis hVS hVB hν hvmin hV hMass hq hq1 hBS hbudget hρ hρ1 hW budget in
theorem giantSignedDoubledChronologicalTrace_exact [Fintype (GiantTwoSidedResidueState PS (k+ell))]
    (θ : ℝ) (f : GiantSignedState PS PB (k+ell) → ℂ) (hf : GiantSignedWordExponential f) (n : ℕ)
    (patterns : Fin n → Finset I) (C : Fin n → I → B → Finset (Fin k))
    (hC : ∀ i v, v ∈ patterns i → ∀ g, (C i v g).card ≤ budget)
    (κ : Fin n → ℤ) (visitQ : Fin (n+1) → ℝ) (ζ : Fin n → ℝ)
    (K : (i : Fin n) → (v : I) → GiantTwoSidedPatternCoefficient PB (C i v) ell)
    (hK : ∀ i v, v ∈ patterns i → ∀ a b aux, ‖K i v a b aux‖ ≤ W)
    (η : (i : Fin n) → (v : I) → (s : GiantSignedState PS PB (k+ell)) →
      GiantSignedRawEdgeMove PS PB ell (C i v) s.2.2 → ℂ)
    (hη : ∀ i v, v ∈ patterns i → ∀ s r, ‖η i v s r‖ ≤ 1)
    (s : GiantSignedState PS PB (k+ell)) :
    let rows := giantSignedChronologicalTraceRows ν V q ρ θ n patterns C κ visitQ ζ K η
    let w : GiantSignedTrace rows s → ℝ := fun t =>
      (2:ℝ)^giantSignedChronologicalTraceBirthTotal ν V q ρ θ n patterns C κ visitQ ζ K η s t *
        ‖giantSignedTraceWeight f rows s t‖
    Summable w ∧ ((∑' t, w t : ℝ) : ℂ) =
      giantSignedDoubledChronologicalWord ν V q ρ θ (fun s => (‖f s‖ : ℂ)) n
        patterns C κ visitQ ζ K
        (fun i v => giantSignedRawEdgeAbsoluteMultiplier ν V (κ i) q ρ θ (ζ i) (K i v) (η i v)) s := by
  dsimp only
  let X := GiantSignedState PS PB (k+ell)
  let degree : X → ℕ := fun s => ∑ g, s.2.2.1 g
  let f' : X → ℂ := fun x => (‖f x‖ : ℂ)
  let rows := giantSignedChronologicalTraceRows ν V q ρ θ n patterns C κ visitQ ζ K η
  let rows' := giantSignedDoubledTraceRows ν V q ρ θ n patterns C κ visitQ ζ K η
  let e := giantSignedDoubledTraceEquiv ν V q ρ θ n patterns C κ visitQ ζ K η s
  let F : GiantSignedTrace rows' s → ℂ := giantSignedTraceWeight f' rows' s
  let w (t : GiantSignedTrace rows s) : ℝ :=
    (2:ℝ)^giantSignedChronologicalTraceBirthTotal ν V q ρ θ n patterns C κ visitQ ζ K η s t *
      ‖giantSignedTraceWeight f rows s t‖
  have hw (t : GiantSignedTrace rows s) : F (e t) = (w t : ℂ) := by
    simpa only [F, e, f', rows, rows', w, Complex.ofReal_mul, Complex.ofReal_pow,
      Complex.ofReal_ofNat] using
      giantSignedDoubledTraceWeight_eq ν hν V q ρ θ f n patterns C κ visitQ ζ K η s t
  have hf' : GiantSignedTraceExponential degree (fun x => ‖f' x‖) := by
    obtain ⟨U,v,hU,hv,he⟩ := hf
    refine ⟨U,v,hU,hv,fun x => ?_⟩
    simpa only [f', Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)] using he x
  have hr := giantSignedDoubledTraceRows_absolute hPS hPB hdis hVS hVB ν hν V
    hvmin hV hMass hq hq1 hBS hbudget hρ hρ1 hW budget θ n patterns C hC κ visitQ ζ K hK η hη
  have hsum := giantSignedTrace_summable_eq degree f' hf' rows' hr
  have hs : Summable (fun t : GiantSignedTrace rows s => ‖F (e t)‖) :=
    (hsum.1 s).comp_injective e.injective
  change Summable w ∧ ((∑' t, w t : ℝ) : ℂ) = _
  refine ⟨hs.congr ?_, ?_⟩
  · intro t
    rw [hw, Complex.norm_real, Real.norm_of_nonneg]
    exact mul_nonneg (pow_nonneg (by norm_num) _) (norm_nonneg _)
  · rw [Complex.ofReal_tsum]
    calc
      _ = ∑' t, F (e t) := tsum_congr (fun t => (hw t).symm)
      _ = ∑' t, F t := e.tsum_eq F
      _ = giantSignedTraceWord rows' f' s := hsum.2.2 s
      _ = _ := congrFun
        (giantSignedDoubledTraceRows_word ν V q ρ θ f' n patterns C κ visitQ ζ K η) s

end
end ArtinMatthews
