module

public import ArtinMatthews.GiantSignedTraceCutoff
public import ArtinMatthews.GiantSignedTraceRows
public import ArtinMatthews.GiantSignedWordDomain
public import ArtinMatthews.GiantSignedTraceEdgeAbsolute
public import ArtinMatthews.GiantSignedTraceGhostAbsolute
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! The original chronological word has an absolutely convergent
dependent move expansion. Removing the common ghost batch bound recovers
that same word with every pattern and every memory degree. -/
namespace ArtinMatthews
open Filter
open scoped BigOperators Topology
noncomputable section

universe u
variable {S B I : Type u} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {M k ell : ℕ}

theorem giantSignedVisitTraceRow_cutoff (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (q ρ : ℝ)
    (H : ℕ) (f : GiantSignedState PS PB M → ℂ) (s : GiantSignedState PS PB M) :
    giantSignedTraceCutoffRowApply H (giantSignedVisitTraceRow ν V q ρ) f s =
      giantSignedGhostBatchCutoff ν (fun _ => ((q / ρ^2 : ℝ) : ℂ))
        (fun g => ((-(1-q) * V g / ρ : ℝ) : ℂ)) (fun _ => ((-(1-q) / ρ : ℝ) : ℂ))
        (fun m => f (s.1,s.2.1,m)) H s.2.2 := by
  classical
  unfold giantSignedTraceCutoffRowApply giantSignedGhostBatchCutoff giantSignedVisitTraceRow
  apply tsum_congr
  intro r
  change GiantSignedGhostMemoryMoves s.2.2 at r
  let z := giantSignedGhostMemoryMoveCoefficient ν (fun _ => ((q / ρ^2 : ℝ) : ℂ))
    (fun g => ((-(1-q) * V g / ρ : ℝ) : ℂ)) (fun _ => ((-(1-q) / ρ : ℝ) : ℂ)) s.2.2 r *
    f (s.1,s.2.1,giantSignedGhostMemoryMoveTarget s.2.2 r)
  change (if Finset.univ.sup (fun g => (r g).2.1) ≤ H then z else 0) =
    if GiantSignedGhostBatchFits H r then z else 0
  have he : (Finset.univ.sup (fun g => (r g).2.1) ≤ H) ↔ GiantSignedGhostBatchFits H r := by
    simp only [Finset.sup_le_iff, Finset.mem_univ, true_implies, GiantSignedGhostBatchFits]
  by_cases hf : GiantSignedGhostBatchFits H r
  · rw [ite_eq_left (he.mpr hf), ite_eq_left hf]
  · rw [ite_eq_right (fun h => hf (he.mp h)), ite_eq_right hf]

theorem giantSignedEdgeTraceRow_cutoff [Fintype (GiantTwoSidedResidueState PS (k+ell))]
    (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (patterns : Finset I)
    (C : I → B → Finset (Fin k)) (κ : ℤ) (q ρ θ ζ : ℝ)
    (K : (v : I) → GiantTwoSidedPatternCoefficient PB (C v) ell)
    (η : (v : I) → (s : GiantSignedState PS PB (k+ell)) →
      GiantSignedRawEdgeMove PS PB ell (C v) s.2.2 → ℂ)
    (H : ℕ) (f : GiantSignedState PS PB (k+ell) → ℂ) :
    giantSignedTraceCutoffRowApply H (giantSignedEdgeTraceRow ν V patterns C κ q ρ θ ζ K η) f =
      giantSignedRawEdgeFamilyApply ν V patterns C κ q ρ θ ζ K η f := by
  rw [← giantSignedEdgeTraceRow_apply]
  funext s
  apply tsum_congr
  intro r
  exact ite_eq_left (Nat.zero_le H)

variable [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
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
theorem giantSignedChronologicalTraceRows_absolute (θ : ℝ) (n : ℕ)
    (patterns : Fin n → Finset I) (C : Fin n → I → B → Finset (Fin k))
    (hC : ∀ i v, v ∈ patterns i → ∀ g, (C i v g).card ≤ budget)
    (κ : Fin n → ℤ) (visitQ : Fin (n+1) → ℝ) (ζ : Fin n → ℝ)
    (K : (i : Fin n) → (v : I) → GiantTwoSidedPatternCoefficient PB (C i v) ell)
    (hK : ∀ i v, v ∈ patterns i → ∀ a b aux, ‖K i v a b aux‖ ≤ W)
    (η : (i : Fin n) → (v : I) → (s : GiantSignedState PS PB (k+ell)) →
      GiantSignedRawEdgeMove PS PB ell (C i v) s.2.2 → ℂ)
    (hη : ∀ i v, v ∈ patterns i → ∀ s r, ‖η i v s r‖ ≤ 1) :
    ∀ r ∈ giantSignedChronologicalTraceRows ν V q ρ θ n patterns C κ visitQ ζ K η,
      GiantSignedTraceRowAbsolute (fun s : GiantSignedState PS PB (k+ell) => ∑ g, s.2.2.1 g) r := by
  induction n with
  | zero =>
      intro r hr
      change r ∈ [giantSignedVisitTraceRow ν V (visitQ 0) ρ] at hr
      rcases List.mem_singleton.mp hr with rfl
      exact giantSignedVisitTraceRow_absolute ν hν V (visitQ 0) ρ
  | succ n ih =>
      intro r hr
      simp only [giantSignedChronologicalTraceRows, List.mem_cons] at hr
      rcases hr with rfl | rfl | hr
      · exact giantSignedVisitTraceRow_absolute ν hν V (visitQ 0) ρ
      · exact giantSignedEdgeTraceRow_absolute hPS hPB hdis hVS hVB ν hν V
          hvmin hV hMass hq hq1 hBS hbudget hρ hρ1 hW budget (patterns 0) (C 0) (hC 0)
          (κ 0) θ (ζ 0) (K 0) (hK 0) (η 0) (hη 0)
      · exact ih (fun i => patterns i.succ) (fun i => C i.succ) (fun i => hC i.succ)
          (fun i => κ i.succ) (fun i => visitQ i.succ) (fun i => ζ i.succ)
          (fun i => K i.succ) (fun i => hK i.succ) (fun i => η i.succ) (fun i => hη i.succ) r hr

include hPS hPB hdis hVS hVB hν hvmin hV hMass hq hq1 hBS hbudget hρ hρ1 hW budget in
theorem giantSignedChronologicalTrace_exact [Fintype (GiantTwoSidedResidueState PS (k+ell))] (θ : ℝ)
    (f : GiantSignedState PS PB (k+ell) → ℂ) (hf : GiantSignedWordExponential f) (n : ℕ)
    (patterns : Fin n → Finset I) (C : Fin n → I → B → Finset (Fin k))
    (hC : ∀ i v, v ∈ patterns i → ∀ g, (C i v g).card ≤ budget)
    (κ : Fin n → ℤ) (visitQ : Fin (n+1) → ℝ) (ζ : Fin n → ℝ)
    (K : (i : Fin n) → (v : I) → GiantTwoSidedPatternCoefficient PB (C i v) ell)
    (hK : ∀ i v, v ∈ patterns i → ∀ a b aux, ‖K i v a b aux‖ ≤ W)
    (η : (i : Fin n) → (v : I) → (s : GiantSignedState PS PB (k+ell)) →
      GiantSignedRawEdgeMove PS PB ell (C i v) s.2.2 → ℂ)
    (hη : ∀ i v, v ∈ patterns i → ∀ s r, ‖η i v s r‖ ≤ 1) :
    let rows := giantSignedChronologicalTraceRows ν V q ρ θ n patterns C κ visitQ ζ K η
    (∀ s, Summable (fun t : GiantSignedTrace rows s => ‖giantSignedTraceWeight f rows s t‖)) ∧
    (∀ s, (∑' t : GiantSignedTrace rows s, giantSignedTraceWeight f rows s t) =
      giantSignedChronologicalWord ν V q ρ θ f n patterns C κ visitQ ζ K η s) ∧
    ∀ s, Tendsto (fun H => giantSignedTraceCutoffWord H rows f s) atTop
      (𝓝 (giantSignedChronologicalWord ν V q ρ θ f n patterns C κ visitQ ζ K η s)) := by
  dsimp only
  let degree := fun s : GiantSignedState PS PB (k+ell) => ∑ g, s.2.2.1 g
  let rows := giantSignedChronologicalTraceRows ν V q ρ θ n patterns C κ visitQ ζ K η
  have hr := giantSignedChronologicalTraceRows_absolute hPS hPB hdis hVS hVB ν hν V
    hvmin hV hMass hq hq1 hBS hbudget hρ hρ1 hW budget θ n patterns C hC κ visitQ ζ K hK η hη
  have hs := giantSignedTrace_summable_eq degree f hf rows hr
  have hw := giantSignedChronologicalTraceRows_word ν V q ρ θ f n patterns C κ visitQ ζ K η
  refine ⟨hs.1, fun s => (hs.2.2 s).trans (congrFun hw s), ?_⟩
  intro s
  rw [← hw]
  exact giantSignedTraceCutoffWord_tendsto degree f hf rows hr s

end
end ArtinMatthews
