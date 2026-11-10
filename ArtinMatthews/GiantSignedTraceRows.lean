module

public import ArtinMatthews.GiantSignedTraceSum
public import ArtinMatthews.GiantSignedChronologicalWord
public import ArtinMatthews.GiantSignedGhostBatchLimit
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

/-! The dependent trace uses precisely the moves of each original
operator. The only batch size recorded is the actual ghost birth size. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

universe u
variable {S B I : Type u} [Fintype S] [Fintype B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {M k ell : ℕ}

def giantSignedGhostTraceRow (ν : ∀ g, PB g → ℝ) (A C D : B → ℂ) :
    GiantSignedTraceRow.{u,u} (GiantSignedState PS PB M) where
  Move s := GiantSignedGhostMemoryMoves s.2.2
  target s r := (s.1, s.2.1, giantSignedGhostMemoryMoveTarget s.2.2 r)
  coefficient s r := giantSignedGhostMemoryMoveCoefficient ν A C D s.2.2 r
  batchSize _ r := Finset.univ.sup (fun g => (r g).2.1)

theorem giantSignedGhostTraceRow_batchSize_le (ν : ∀ g, PB g → ℝ) (A C D : B → ℂ)
    (s : GiantSignedState PS PB M) (r : GiantSignedGhostMemoryMoves s.2.2) (H : ℕ) :
    (giantSignedGhostTraceRow ν A C D).batchSize s r ≤ H ↔ GiantSignedGhostBatchFits H r := by
  change (Finset.univ.sup fun g => (r g).2.1) ≤ H ↔ _
  simp only [Finset.sup_le_iff, Finset.mem_univ, true_implies, GiantSignedGhostBatchFits]

def giantSignedVisitTraceRow (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (q ρ : ℝ) :
    GiantSignedTraceRow.{u,u} (GiantSignedState PS PB M) :=
  giantSignedGhostTraceRow ν (fun _ => ((q / ρ^2 : ℝ) : ℂ))
    (fun g => ((-(1-q) * V g / ρ : ℝ) : ℂ)) (fun _ => ((-(1-q) / ρ : ℝ) : ℂ))

variable [DecidableEq S] [DecidableEq B]

theorem giantSignedVisitTraceRow_apply (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (q ρ : ℝ)
    (f : GiantSignedState PS PB M → ℂ) :
    giantSignedTraceRowApply (giantSignedVisitTraceRow ν V q ρ) f =
      giantSignedChronologicalVisit ν V q ρ f := rfl

def giantSignedEdgeTraceRow (ν : ∀ g, PB g → ℝ) (V : B → ℝ)
    (patterns : Finset I) (C : I → B → Finset (Fin k)) (κ : ℤ) (q ρ θ ζ : ℝ)
    (K : (v : I) → GiantTwoSidedPatternCoefficient PB (C v) ell)
    (η : (v : I) → (s : GiantSignedState PS PB (k+ell)) →
      GiantSignedRawEdgeMove PS PB ell (C v) s.2.2 → ℂ) :
    GiantSignedTraceRow.{u,u} (GiantSignedState PS PB (k+ell)) where
  Move s := Σ v : patterns, GiantSignedRawEdgeMove PS PB ell (C v.val) s.2.2
  target s r := giantSignedRawEdgeTarget κ s r.2
  coefficient s r := giantSignedRawEdgeCoefficient ν V κ q ρ θ ζ (K r.1.val) s r.2 * η r.1.val s r.2
  batchSize _ _ := 0

variable [Fintype (GiantTwoSidedResidueState PS (k+ell))]

theorem giantSignedEdgeTraceRow_apply (ν : ∀ g, PB g → ℝ) (V : B → ℝ)
    (patterns : Finset I) (C : I → B → Finset (Fin k)) (κ : ℤ) (q ρ θ ζ : ℝ)
    (K : (v : I) → GiantTwoSidedPatternCoefficient PB (C v) ell)
    (η : (v : I) → (s : GiantSignedState PS PB (k+ell)) →
      GiantSignedRawEdgeMove PS PB ell (C v) s.2.2 → ℂ)
    (f : GiantSignedState PS PB (k+ell) → ℂ) :
    giantSignedTraceRowApply (giantSignedEdgeTraceRow ν V patterns C κ q ρ θ ζ K η) f =
      giantSignedRawEdgeFamilyApply ν V patterns C κ q ρ θ ζ K η f := by
  classical
  funext s
  change (∑' r : Σ v : patterns, GiantSignedRawEdgeMove PS PB ell (C v.val) s.2.2,
    giantSignedRawEdgeCoefficient ν V κ q ρ θ ζ (K r.1.val) s r.2 * η r.1.val s r.2 *
      f (giantSignedRawEdgeTarget κ s r.2)) = _
  rw [tsum_fintype, Fintype.sum_sigma]
  unfold giantSignedRawEdgeFamilyApply giantSignedRawEdgeApply
  let F (v : I) : ℂ := ∑ r : GiantSignedRawEdgeMove PS PB ell (C v) s.2.2,
    giantSignedRawEdgeCoefficient ν V κ q ρ θ ζ (K v) s r * η v s r * f (giantSignedRawEdgeTarget κ s r)
  exact Finset.sum_coe_sort patterns F

def giantSignedChronologicalTraceRows (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (q ρ θ : ℝ) :
    (n : ℕ) → (patterns : Fin n → Finset I) → (C : Fin n → I → B → Finset (Fin k)) →
      (κ : Fin n → ℤ) → (visitQ : Fin (n+1) → ℝ) → (ζ : Fin n → ℝ) →
      ((i : Fin n) → (v : I) → GiantTwoSidedPatternCoefficient PB (C i v) ell) →
      ((i : Fin n) → (v : I) → (s : GiantSignedState PS PB (k+ell)) →
        GiantSignedRawEdgeMove PS PB ell (C i v) s.2.2 → ℂ) →
      List (GiantSignedTraceRow.{u,u} (GiantSignedState PS PB (k+ell)))
  | 0, _, _, _, visitQ, _, _, _ => [giantSignedVisitTraceRow ν V (visitQ 0) ρ]
  | n+1, patterns, C, κ, visitQ, ζ, K, η =>
      giantSignedVisitTraceRow ν V (visitQ 0) ρ ::
        giantSignedEdgeTraceRow ν V (patterns 0) (C 0) (κ 0) q ρ θ (ζ 0) (K 0) (η 0) ::
        giantSignedChronologicalTraceRows ν V q ρ θ n (fun i => patterns i.succ)
          (fun i => C i.succ) (fun i => κ i.succ) (fun i => visitQ i.succ)
          (fun i => ζ i.succ) (fun i => K i.succ) (fun i => η i.succ)

theorem giantSignedChronologicalTraceRows_word (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (q ρ θ : ℝ)
    (f : GiantSignedState PS PB (k+ell) → ℂ) (n : ℕ)
    (patterns : Fin n → Finset I) (C : Fin n → I → B → Finset (Fin k))
    (κ : Fin n → ℤ) (visitQ : Fin (n+1) → ℝ) (ζ : Fin n → ℝ)
    (K : (i : Fin n) → (v : I) → GiantTwoSidedPatternCoefficient PB (C i v) ell)
    (η : (i : Fin n) → (v : I) → (s : GiantSignedState PS PB (k+ell)) →
      GiantSignedRawEdgeMove PS PB ell (C i v) s.2.2 → ℂ) :
    giantSignedTraceWord (giantSignedChronologicalTraceRows ν V q ρ θ n patterns C κ visitQ ζ K η) f =
      giantSignedChronologicalWord ν V q ρ θ f n patterns C κ visitQ ζ K η := by
  induction n with
  | zero => exact giantSignedVisitTraceRow_apply ν V (visitQ 0) ρ f
  | succ n ih =>
      simp only [giantSignedChronologicalTraceRows, giantSignedTraceWord, List.foldr_cons,
        giantSignedVisitTraceRow_apply, giantSignedEdgeTraceRow_apply, giantSignedChronologicalWord_succ]
      rw [← giantSignedTraceWord, ih]

end
end ArtinMatthews
