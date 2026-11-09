module

public import ArtinMatthews.GiantSignedDoubledTraceActual
public import ArtinMatthews.GiantSignedTraceBirthBudget
public import ArtinMatthews.GiantSignedTraceOmission
public import ArtinMatthews.GiantSignedTraceMemoryProjection


set_option backward.privateInPublic true
@[expose] public section

/-! The actual memory-cap error is paid for by the actual doubled word.
The bound still holds with a global distinct-birth indicator in the trace. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

universe u
variable {S B I : Type u} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell : ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
    [∀ g, ∀ p : PB g, NeZero p.val]
    [Fintype (GiantTwoSidedResidueState PS (k+ell))]
    (hPS : ∀ j p, p ∈ PS j → p.Prime) (hPB : ∀ j p, p ∈ PB j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (PS i) (PS j)))
    (hVS : ∀ j, 0 < bandReciprocalMass (PS j)) (hVB : ∀ g, 0 < bandReciprocalMass (PB g))
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (V : B → ℝ)
    {vmin massMax q ρ BS W : ℝ} (hvmin : 0 < vmin) (hV : ∀ g, vmin ≤ V g)
    (hMass : ∀ g, (∑ p : PB g, ν g p) ≤ massMax)
    (hq : 0 < q) (hq1 : q ≤ 1) (hBS : 0 ≤ BS)
    (hbudget : ∀ j (z : ℕ), (bandReciprocalMass (PS j))⁻¹ ^ ell *
      ((z : ℝ) + (ell : ℝ)) ^ ell * q ^ ((z : ℝ) / 2) ≤ BS)
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hW : 0 ≤ W) (budget H : ℕ)
    (θ : ℝ) (f : GiantSignedState PS PB (k+ell) → ℂ) (hf : GiantSignedWordExponential f) (n : ℕ)
    (patterns : Fin n → Finset I) (C : Fin n → I → B → Finset (Fin k))
    (hC : ∀ i v, v ∈ patterns i → ∀ g, (C i v g).card ≤ budget)
    (κ : Fin n → ℤ) (visitQ : Fin (n+1) → ℝ) (ζ : Fin n → ℝ)
    (K : (i : Fin n) → (v : I) → GiantTwoSidedPatternCoefficient PB (C i v) ell)
    (hK : ∀ i v, v ∈ patterns i → ∀ a b aux, ‖K i v a b aux‖ ≤ W)
    (η : (i : Fin n) → (v : I) → (s : GiantSignedState PS PB (k+ell)) →
      GiantSignedRawEdgeMove PS PB ell (C i v) s.2.2 → ℂ)
    (hη : ∀ i v, v ∈ patterns i → ∀ s r, ‖η i v s r‖ ≤ 1)
    (s : GiantSignedState PS PB (k+ell)) (hs : s.2.2 = giantSignedEmptyMemory PB)

include hPS hPB hdis hVS hVB hν hvmin hV hMass hq hq1 hBS hbudget hρ hρ1 hW hf hC hK hη hs in
theorem giantSignedChronologicalTraceOmission_le
    (φ : GiantSignedTrace (giantSignedChronologicalTraceRows ν V q ρ θ n patterns C κ visitQ ζ K η) s → ℂ)
    (hφ : ∀ t, ‖φ t‖ ≤ 1) :
    let rows := giantSignedChronologicalTraceRows ν V q ρ θ n patterns C κ visitQ ζ K η
    let good := GiantSignedTraceWithin (fun s => (∑ g, s.2.2.1 g) ≤ H) rows s
    ‖(∑' t : GiantSignedTrace rows s, giantSignedTraceWeight f rows s t * φ t) -
        (∑' t : GiantSignedTrace rows s,
          if good t then giantSignedTraceWeight f rows s t * φ t else 0)‖ ≤
      (giantSignedDoubledChronologicalWord ν V q ρ θ (fun x => (‖f x‖ : ℂ)) n patterns C κ visitQ ζ K
        (fun i v => giantSignedRawEdgeAbsoluteMultiplier ν V (κ i) q ρ θ (ζ i) (K i v) (η i v)) s).re /
          (2:ℝ)^(H-(ell+budget)*Fintype.card B*n) := by
  dsimp only
  have ho := giantSignedChronologicalTrace_exact hPS hPB hdis hVS hVB ν hν V
    hvmin hV hMass hq hq1 hBS hbudget hρ hρ1 hW budget θ f hf n patterns C hC κ visitQ ζ K hK η hη
  have hd := giantSignedDoubledChronologicalTrace_exact hPS hPB hdis hVS hVB ν hν V
    hvmin hV hMass hq hq1 hBS hbudget hρ hρ1 hW budget θ f hf n patterns C hC κ visitQ ζ K hK η hη s
  let rows := giantSignedChronologicalTraceRows ν V q ρ θ n patterns C κ visitQ ζ K η
  let b := giantSignedChronologicalTraceBirthTotal ν V q ρ θ n patterns C κ visitQ ζ K η s
  let w := giantSignedTraceWeight f rows s
  let good := GiantSignedTraceWithin (fun s => (∑ g, s.2.2.1 g) ≤ H) rows s
  have hfail (t : GiantSignedTrace rows s) (ht : ¬ good t) :
      H < b t + (ell+budget)*Fintype.card B*n :=
    giantSignedChronologicalTrace_cap_failure_births ν V q ρ θ budget H n patterns C hC κ visitQ ζ K η s t hs ht
  refine (giantSignedTraceOmission_norm_le w φ good b H ((ell+budget)*Fintype.card B*n)
    hφ (ho.1 s) hd.1 hfail).trans_eq ?_
  have hreal := congrArg Complex.re hd.2
  exact congrArg (fun v : ℝ => v / (2:ℝ)^(H-(ell+budget)*Fintype.card B*n))
    (by simpa only [Complex.ofReal_re] using hreal)

include hPS hPB hdis hVS hVB hν hvmin hV hMass hq hq1 hBS hbudget hρ hρ1 hW hf hC hK hη hs in
theorem giantSignedChronologicalWord_projection_error :
    ‖giantSignedChronologicalWord ν V q ρ θ f n patterns C κ visitQ ζ K η s -
      giantSignedProjectedChronologicalWord H ν V q ρ θ f n patterns C κ visitQ ζ K η s‖ ≤
      (giantSignedDoubledChronologicalWord ν V q ρ θ (fun x => (‖f x‖ : ℂ)) n patterns C κ visitQ ζ K
        (fun i v => giantSignedRawEdgeAbsoluteMultiplier ν V (κ i) q ρ θ (ζ i) (K i v) (η i v)) s).re /
          (2:ℝ)^(H-(ell+budget)*Fintype.card B*n) := by
  have ho := giantSignedChronologicalTrace_exact hPS hPB hdis hVS hVB ν hν V
    hvmin hV hMass hq hq1 hBS hbudget hρ hρ1 hW budget θ f hf n patterns C hC κ visitQ ζ K hK η hη
  have hr := giantSignedChronologicalTraceRows_absolute hPS hPB hdis hVS hVB ν hν V
    hvmin hV hMass hq hq1 hBS hbudget hρ hρ1 hW budget θ n patterns C hC κ visitQ ζ K hK η hη
  have hp := giantSignedProjectedChronologicalWord_trace H ν V q ρ θ f hf n
    patterns C κ visitQ ζ K η hr s
  have he := giantSignedChronologicalTraceOmission_le hPS hPB hdis hVS hVB ν hν V
    hvmin hV hMass hq hq1 hBS hbudget hρ hρ1 hW budget H θ f hf n patterns C hC κ visitQ ζ K hK η hη
    s hs (fun _ => 1) (fun _ => norm_one.le)
  rw [← ho.2.1 s, hp]
  simpa only [mul_one] using he

end
end ArtinMatthews
