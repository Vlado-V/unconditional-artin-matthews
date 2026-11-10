module

public import ArtinMatthews.GiantSignedTraceMemo
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

/-! The memo rules follow every visit and edge of the original
alternating trace, with the exact product of their separate costs. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section

universe u
variable {S B I M : Type u} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell : ℕ}

def giantSignedChronologicalMemoRules (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (q ρ θ : ℝ) :
    (n : ℕ) → (patterns : Fin n → Finset I) → (C : Fin n → I → B → Finset (Fin k)) →
      (κ : Fin n → ℤ) → (visitQ : Fin (n+1) → ℝ) → (ζ : Fin n → ℝ) →
      (K : (i : Fin n) → (v : I) → GiantTwoSidedPatternCoefficient PB (C i v) ell) →
      (η : (i : Fin n) → (v : I) → (s : GiantSignedState PS PB (k+ell)) →
        GiantSignedRawEdgeMove PS PB ell (C i v) s.2.2 → ℂ) →
      ((i : Fin (n+1)) → GiantSignedTraceMemoRule M (giantSignedVisitTraceRow (PS := PS) (M := k+ell) ν V (visitQ i) ρ)) →
      ((i : Fin n) → GiantSignedTraceMemoRule M
        (giantSignedEdgeTraceRow ν V (patterns i) (C i) (κ i) q ρ θ (ζ i) (K i) (η i))) →
      GiantSignedTraceMemoRules M (giantSignedChronologicalTraceRows ν V q ρ θ n patterns C κ visitQ ζ K η)
  | 0, _, _, _, _, _, _, _, G, _ => (G 0,PUnit.unit)
  | n+1, patterns, C, κ, visitQ, ζ, K, η, G, E =>
      (G 0,E 0,giantSignedChronologicalMemoRules ν V q ρ θ n (fun i => patterns i.succ)
        (fun i => C i.succ) (fun i => κ i.succ) (fun i => visitQ i.succ) (fun i => ζ i.succ)
        (fun i => K i.succ) (fun i => η i.succ) (fun i => G i.succ) (fun i => E i.succ))

variable (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (q ρ θ : ℝ)
    (n : ℕ) (patterns : Fin n → Finset I) (C : Fin n → I → B → Finset (Fin k))
    (κ : Fin n → ℤ) (visitQ : Fin (n+1) → ℝ) (ζ : Fin n → ℝ)
    (K : (i : Fin n) → (v : I) → GiantTwoSidedPatternCoefficient PB (C i v) ell)
    (η : (i : Fin n) → (v : I) → (s : GiantSignedState PS PB (k+ell)) →
      GiantSignedRawEdgeMove PS PB ell (C i v) s.2.2 → ℂ)
    (G : (i : Fin (n+1)) →
      GiantSignedTraceMemoRule M (giantSignedVisitTraceRow (PS := PS) (M := k+ell) ν V (visitQ i) ρ))
    (E : (i : Fin n) →
      GiantSignedTraceMemoRule M (giantSignedEdgeTraceRow ν V (patterns i) (C i) (κ i) q ρ θ (ζ i) (K i) (η i)))

local notation "Rows" => giantSignedChronologicalTraceRows ν V q ρ θ n patterns C κ visitQ ζ K η
local notation "Rules" => giantSignedChronologicalMemoRules ν V q ρ θ n patterns C κ visitQ ζ K η G E

theorem giantSignedChronologicalMemoRules_cost :
    giantSignedTraceMemoCost Rows Rules = (∏ i, (G i).cost) * ∏ i, (E i).cost := by
  induction n with
  | zero =>
      change (G 0).cost * 1 = (∏ i : Fin 1, (G i).cost) * ∏ i : Fin 0, (E i).cost
      rw [Fin.prod_univ_one, Fin.prod_univ_zero]
  | succ n ih =>
      have ht := ih (fun i => patterns i.succ) (fun i => C i.succ) (fun i => κ i.succ)
        (fun i => visitQ i.succ) (fun i => ζ i.succ) (fun i => K i.succ) (fun i => η i.succ)
        (fun i => G i.succ) (fun i => E i.succ)
      let a := (G 0).cost
      let b := (E 0).cost
      let A := ∏ i : Fin (n+1), (G i.succ).cost
      let B := ∏ i : Fin n, (E i.succ).cost
      calc
        _ = a * (b * (A * B)) := congrArg (fun z => a * (b * z)) ht
        _ = (a * A) * (b * B) := by ac_rfl
        _ = _ := congrArg₂ (· * ·) (Fin.prod_univ_succ (fun i : Fin (n+2) => (G i).cost)).symm
          (Fin.prod_univ_succ (fun i : Fin (n+1) => (E i).cost)).symm

theorem giantSignedChronologicalMemoRules_absolute (w : GiantSignedState PS PB (k+ell) → ℝ≥0∞)
    (hG : ∀ i, GiantSignedTraceMemoAbsolute w [giantSignedVisitTraceRow ν V (visitQ i) ρ] (G i,PUnit.unit))
    (hE : ∀ i, GiantSignedTraceMemoAbsolute w
      [giantSignedEdgeTraceRow ν V (patterns i) (C i) (κ i) q ρ θ (ζ i) (K i) (η i)] (E i,PUnit.unit)) :
    GiantSignedTraceMemoAbsolute w Rows Rules := by
  induction n with
  | zero => exact hG 0
  | succ n ih =>
      exact ⟨(hG 0).1,(hE 0).1,
        ih (fun i => patterns i.succ) (fun i => C i.succ) (fun i => κ i.succ)
          (fun i => visitQ i.succ) (fun i => ζ i.succ) (fun i => K i.succ) (fun i => η i.succ)
          (fun i => G i.succ) (fun i => E i.succ) (fun i => hG i.succ) (fun i => hE i.succ)⟩

end
end ArtinMatthews
