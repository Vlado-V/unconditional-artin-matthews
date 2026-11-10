module

public import ArtinMatthews.GiantSignedTraceMultipliers
public import ArtinMatthews.GiantSignedProjectedBirthWord
public import ArtinMatthews.GiantSignedTraceRows
public import ArtinMatthews.GiantSignedTraceMemoryProjection
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


set_option backward.privateInPublic true
@[expose] public section

/-! The projected phased word is an exact reweighting of the original
capped traces. Both families of multipliers are read on actual moves. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

universe u
variable {S B I : Type u} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell M : ℕ}

theorem giantSignedBirthVisitTraceRow_projected (H : ℕ) (ν : ∀ g, PB g → ℝ) (V : B → ℝ)
    (qi ρ : ℝ) (φ : GiantSignedGhostBirthMultiplier PB) (f : GiantSignedState PS PB M → ℂ) :
    giantSignedTraceProjectedRowApply (fun s => (∑ g, s.2.2.1 g) ≤ H)
      (giantSignedTraceMultiplyRow (giantSignedVisitTraceRow ν V qi ρ)
        (fun _ r => φ (fun g => (r g).2.1) (fun g => (r g).2.2))) f =
      giantSignedProjectedBirthVisit H ν V qi ρ φ f := by
  simp only [giantSignedTraceProjectedRowApply, giantSignedTraceProject_memory]
  rfl

def giantSignedChronologicalTraceMultipliers (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (q ρ θ : ℝ) :
    (n : ℕ) → (patterns : Fin n → Finset I) → (C : Fin n → I → B → Finset (Fin k)) →
      (κ : Fin n → ℤ) → (visitQ : Fin (n+1) → ℝ) → (ζ : Fin n → ℝ) →
      (K : (i : Fin n) → (v : I) → GiantTwoSidedPatternCoefficient PB (C i v) ell) →
      (η : (i : Fin n) → (v : I) → (s : GiantSignedState PS PB (k+ell)) →
        GiantSignedRawEdgeMove PS PB ell (C i v) s.2.2 → ℂ) →
      ((i : Fin n) → (v : I) → (s : GiantSignedState PS PB (k+ell)) →
        GiantSignedRawEdgeMove PS PB ell (C i v) s.2.2 → ℂ) →
      (Fin (n+1) → GiantSignedGhostBirthMultiplier PB) →
      GiantSignedTraceMultipliers (giantSignedChronologicalTraceRows ν V q ρ θ n patterns C κ visitQ ζ K η)
  | 0, _, _, _, _, _, _, _, _, φ =>
      (fun _ r => φ 0 (fun g => (r g).2.1) (fun g => (r g).2.2), PUnit.unit)
  | n+1, patterns, C, κ, visitQ, ζ, K, η, ψ, φ =>
      (fun _ r => φ 0 (fun g => (r g).2.1) (fun g => (r g).2.2),
        fun s r => ψ 0 r.1.val s r.2,
        giantSignedChronologicalTraceMultipliers ν V q ρ θ n (fun i => patterns i.succ)
          (fun i => C i.succ) (fun i => κ i.succ) (fun i => visitQ i.succ) (fun i => ζ i.succ)
          (fun i => K i.succ) (fun i => η i.succ) (fun i => ψ i.succ) (fun i => φ i.succ))

variable (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (q ρ θ : ℝ)
    (n : ℕ) (patterns : Fin n → Finset I) (C : Fin n → I → B → Finset (Fin k))
    (κ : Fin n → ℤ) (visitQ : Fin (n+1) → ℝ) (ζ : Fin n → ℝ)
    (K : (i : Fin n) → (v : I) → GiantTwoSidedPatternCoefficient PB (C i v) ell)
    (η ψ : (i : Fin n) → (v : I) → (s : GiantSignedState PS PB (k+ell)) →
      GiantSignedRawEdgeMove PS PB ell (C i v) s.2.2 → ℂ)
    (φ : Fin (n+1) → GiantSignedGhostBirthMultiplier PB)

theorem giantSignedChronologicalTraceMultipliers_bounded
    (hψ : ∀ i v, v ∈ patterns i → ∀ s r, ‖ψ i v s r‖ ≤ 1)
    (hφ : ∀ i b p, ‖φ i b p‖ ≤ 1) :
    GiantSignedTraceMultipliersBounded
      (giantSignedChronologicalTraceRows ν V q ρ θ n patterns C κ visitQ ζ K η)
      (giantSignedChronologicalTraceMultipliers ν V q ρ θ n patterns C κ visitQ ζ K η ψ φ) := by
  induction n with
  | zero => exact ⟨fun _ r => hφ 0 _ _, trivial⟩
  | succ n ih =>
      exact ⟨fun _ r => hφ 0 _ _, fun s r => hψ 0 r.1.val r.1.property s r.2,
        ih (fun i => patterns i.succ) (fun i => C i.succ) (fun i => κ i.succ)
          (fun i => visitQ i.succ) (fun i => ζ i.succ) (fun i => K i.succ)
          (fun i => η i.succ) (fun i => ψ i.succ) (fun i => φ i.succ)
          (fun i => hψ i.succ) (fun i => hφ i.succ)⟩

variable [Fintype (GiantTwoSidedResidueState PS (k+ell))]

theorem giantSignedBirthTraceRows_projected (H : ℕ) (f : GiantSignedState PS PB (k+ell) → ℂ) :
    let rows := giantSignedChronologicalTraceRows ν V q ρ θ n patterns C κ visitQ ζ K η
    let φ' := giantSignedChronologicalTraceMultipliers ν V q ρ θ n patterns C κ visitQ ζ K η ψ φ
    giantSignedTraceProjectedWord (fun s => (∑ g, s.2.2.1 g) ≤ H)
      (giantSignedTraceMultiplyRows rows φ') f =
      giantSignedProjectedBirthChronologicalWord H ν V q ρ θ f n patterns C κ visitQ ζ K
        (fun i v s r => η i v s r * ψ i v s r) φ := by
  dsimp only
  induction n with
  | zero => exact giantSignedBirthVisitTraceRow_projected H ν V (visitQ 0) ρ (φ 0) f
  | succ n ih =>
      have he : giantSignedTraceMultiplyRow
          (giantSignedEdgeTraceRow ν V (patterns 0) (C 0) (κ 0) q ρ θ (ζ 0) (K 0) (η 0))
          (fun s r => ψ 0 r.1.val s r.2) =
        giantSignedEdgeTraceRow ν V (patterns 0) (C 0) (κ 0) q ρ θ (ζ 0) (K 0)
          (fun v s r => η 0 v s r * ψ 0 v s r) := by
        simp only [giantSignedTraceMultiplyRow, giantSignedEdgeTraceRow, mul_assoc]
      simp only [giantSignedChronologicalTraceRows, giantSignedChronologicalTraceMultipliers,
        giantSignedTraceMultiplyRows, giantSignedTraceProjectedWord, List.foldr_cons,
        giantSignedBirthVisitTraceRow_projected, he, giantSignedEdgeTraceRow_projected,
        giantSignedProjectedBirthChronologicalWord]
      rw [← giantSignedTraceProjectedWord, ih]

theorem giantSignedProjectedBirthChronologicalWord_trace (H : ℕ)
    (f : GiantSignedState PS PB (k+ell) → ℂ) (hf : GiantSignedWordExponential f)
    (hψ : ∀ i v, v ∈ patterns i → ∀ s r, ‖ψ i v s r‖ ≤ 1)
    (hφ : ∀ i b p, ‖φ i b p‖ ≤ 1)
    (hr : ∀ r ∈ giantSignedChronologicalTraceRows ν V q ρ θ n patterns C κ visitQ ζ K η,
      GiantSignedTraceRowAbsolute (fun s => ∑ g, s.2.2.1 g) r)
    (s : GiantSignedState PS PB (k+ell)) :
    let rows := giantSignedChronologicalTraceRows ν V q ρ θ n patterns C κ visitQ ζ K η
    let φ' := giantSignedChronologicalTraceMultipliers ν V q ρ θ n patterns C κ visitQ ζ K η ψ φ
    giantSignedProjectedBirthChronologicalWord H ν V q ρ θ f n patterns C κ visitQ ζ K
      (fun i v s r => η i v s r * ψ i v s r) φ s =
      ∑' t : GiantSignedTrace rows s,
        if GiantSignedTraceWithin (fun x => (∑ g, x.2.2.1 g) ≤ H) rows s t then
          giantSignedTraceWeight f rows s t * giantSignedTraceMultipliersProduct rows φ' s t else 0 := by
  dsimp only
  rw [← giantSignedBirthTraceRows_projected ν V q ρ θ n patterns C κ visitQ ζ K η ψ φ H f]
  exact giantSignedTraceMultiplyProjectedWord_eq _ f hf _ hr _
    (giantSignedChronologicalTraceMultipliers_bounded ν V q ρ θ n patterns C κ visitQ ζ K η ψ φ hψ hφ) _ s

end
end ArtinMatthews
