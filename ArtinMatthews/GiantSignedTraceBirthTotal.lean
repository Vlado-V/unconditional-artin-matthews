module

public import ArtinMatthews.GiantSignedTraceRows
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

/-! Total ghost births are counted on the literal trace. Every visit
and edge has its original target and every group its actual batch size. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

universe u
variable {S B I : Type u} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell M : ℕ}

theorem giantSignedGhostTraceRow_degree_le (ν : ∀ g, PB g → ℝ) (A C D : B → ℂ)
    (s : GiantSignedState PS PB M) (r : GiantSignedGhostMemoryMoves s.2.2) :
    (∑ g, ((giantSignedGhostTraceRow ν A C D).target s r).2.2.1 g) ≤
      (∑ g, s.2.2.1 g) + (∑ g, (r g).2.1) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro g _
  change (giantSignedGhostTarget (giantSignedMemoryGroupEquiv PB s.2.2 g)
    (r g).1 (r g).2.2).1 ≤ _
  rw [giantSignedGhostTarget_degree]
  change s.2.2.1 g - (r g).1.card + (r g).2.1 ≤ _
  omega

theorem giantSignedRawEdgeTarget_degree_le {C : B → Finset (Fin k)}
    (κ : ℤ) (s : GiantSignedState PS PB (k+ell)) (r : GiantSignedRawEdgeMove PS PB ell C s.2.2)
    (budget : ℕ) (hC : ∀ g, (C g).card ≤ budget) :
    (∑ g, (giantSignedRawEdgeTarget κ s r).2.2.1 g) ≤
      (∑ g, s.2.2.1 g) + (ell+budget) * Fintype.card B := by
  have hc : (∑ _g : B, (ell+budget)) = (ell+budget) * Fintype.card B := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact Nat.mul_comm _ _
  rw [← hc, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro g _
  have hs : (r.choice.1 g).card ≤ ell+(C g).card := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_le_card (Finset.subset_univ (r.choice.1 g))
  have he := giantSignedEdgeTarget_degree
    (κ * (giantSignedRawEdgeProduct s r : ℤ)) s.2.2
    (giantSignedPatternFreeLabels C (giantSignedRawEdgeBigSource s r)) r.choice g
  change (giantSignedRawEdgeTarget κ s r).2.2.1 g = _ at he
  exact he.le.trans (Nat.add_le_add (Nat.sub_le _ _) (hs.trans (Nat.add_le_add_left (hC g) ell)))

def giantSignedChronologicalTraceBirthTotal (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (q ρ θ : ℝ) :
    (n : ℕ) → (patterns : Fin n → Finset I) → (C : Fin n → I → B → Finset (Fin k)) →
      (κ : Fin n → ℤ) → (visitQ : Fin (n+1) → ℝ) → (ζ : Fin n → ℝ) →
      (K : (i : Fin n) → (v : I) → GiantTwoSidedPatternCoefficient PB (C i v) ell) →
      (η : (i : Fin n) → (v : I) → (s : GiantSignedState PS PB (k+ell)) →
        GiantSignedRawEdgeMove PS PB ell (C i v) s.2.2 → ℂ) →
      (s : GiantSignedState PS PB (k+ell)) →
      GiantSignedTrace (giantSignedChronologicalTraceRows ν V q ρ θ n patterns C κ visitQ ζ K η) s → ℕ
  | 0, _, _, _, _, _, _, _, s, t => by
      change (Σ _ : GiantSignedGhostMemoryMoves s.2.2, PUnit) at t
      exact ∑ g, (t.1 g).2.1
  | n+1, patterns, C, κ, visitQ, ζ, K, η, s, t => by
      let G := giantSignedVisitTraceRow (PS := PS) (M := k+ell) ν V (visitQ 0) ρ
      let E := giantSignedEdgeTraceRow ν V (patterns 0) (C 0) (κ 0) q ρ θ (ζ 0) (K 0) (η 0)
      let rest := giantSignedChronologicalTraceRows ν V q ρ θ n (fun i => patterns i.succ)
        (fun i => C i.succ) (fun i => κ i.succ) (fun i => visitQ i.succ) (fun i => ζ i.succ)
        (fun i => K i.succ) (fun i => η i.succ)
      change (Σ r : G.Move s, Σ e : E.Move (G.target s r),
        GiantSignedTrace rest (E.target (G.target s r) e)) at t
      exact (∑ g, (t.1 g).2.1) +
        giantSignedChronologicalTraceBirthTotal ν V q ρ θ n (fun i => patterns i.succ)
          (fun i => C i.succ) (fun i => κ i.succ) (fun i => visitQ i.succ) (fun i => ζ i.succ)
          (fun i => K i.succ) (fun i => η i.succ) (E.target (G.target s t.1) t.2.1) t.2.2

end
end ArtinMatthews
