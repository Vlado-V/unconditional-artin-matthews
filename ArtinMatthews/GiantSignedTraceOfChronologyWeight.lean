module

public import ArtinMatthews.GiantSignedTraceOfChronology
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

/-! The replayed trace has exactly the original chronological
coefficient, including the terminal empty-memory value. -/

namespace ArtinMatthews
open scoped BigOperators
noncomputable section

universe u v

private theorem traceWeight_cast {X : Type u} (f : X → ℂ) (rows : List (GiantSignedTraceRow.{u,v} X))
    {x y : X} (h : x = y) (t : GiantSignedTrace rows y) :
    giantSignedTraceWeight f rows x (cast (congrArg (GiantSignedTrace rows) h.symm) t) =
      giantSignedTraceWeight f rows y t := by
  subst y
  rfl

variable {S B I : Type u} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell : ℕ}

local notation "One" => fun _ _ _ _ => (1 : ℂ)

theorem giantSignedTraceOfChronology_weight (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (q ρ θ : ℝ)
    (n : ℕ) (patterns : Fin n → Finset I) (C : Fin n → I → B → Finset (Fin k))
    (κ : Fin n → ℤ) (visitQ : Fin (n+1) → ℝ) (ζ : Fin n → ℝ)
    (K : (i : Fin n) → (a : I) → GiantTwoSidedPatternCoefficient PB (C i a) ell)
    (p : (i : Fin n) → patterns i) (batch : Fin (n+1) → B → ℕ)
    (h : GiantSignedChronologicalChoices PS PB ell (fun i => C i (p i).val) batch)
    (hc : GiantSignedChronologicalCompatible κ h)
    (hb : giantSignedChronologicalGhostTarget h (Fin.last n) = giantSignedEmptyMemory PB) :
    giantSignedTraceWeight giantSignedBoundary
      (giantSignedChronologicalTraceRows ν V q ρ θ n patterns C κ visitQ ζ K One) (h.state 0)
      (giantSignedTraceOfChronology ν V q ρ θ n patterns C κ visitQ ζ K p batch h hc) =
        (∏ i, giantSignedChronologicalGhostCoefficient ν V visitQ ρ h i) *
          ∏ i, giantSignedChronologicalEdgeCoefficient ν V κ q ρ θ ζ (fun i => K i (p i).val) h i := by
  induction n with
  | zero =>
    let s := giantSignedChronologicalAfterVisitState h 0
    have hs : giantSignedBoundary s = 1 := by
      unfold giantSignedBoundary
      exact ite_eq_left (show s.2.2 = giantSignedEmptyMemory PB from hb)
    change giantSignedChronologicalGhostCoefficient ν V visitQ ρ h 0 * giantSignedBoundary s = _
    simp only [hs,Fin.prod_univ_zero,mul_one]
    rw [Fin.prod_univ_succ]
    simp only [Fin.prod_univ_zero,mul_one]
  | succ n ih =>
    let a := giantSignedChronologicalAfterVisitState h (0 : Fin (n+1)).castSucc
    let r := giantSignedChronologicalRawMove h (0 : Fin (n+1))
    let x := giantSignedRawEdgeTarget (κ 0) a r
    let y := h.state (0 : Fin (n+1)).succ
    have hxy : x = y := giantSignedChronologicalRawMove_target κ h hc 0
    let rest := giantSignedChronologicalTraceRows (PS := PS) ν V q ρ θ n (fun i => patterns i.succ)
      (fun i => C i.succ) (fun i => κ i.succ) (fun i => visitQ i.succ) (fun i => ζ i.succ)
      (fun i => K i.succ) One
    let t : GiantSignedTrace rest y := giantSignedTraceOfChronology ν V q ρ θ n (fun i => patterns i.succ)
      (fun i => C i.succ) (fun i => κ i.succ) (fun i => visitQ i.succ) (fun i => ζ i.succ)
      (fun i => K i.succ) (fun i => p i.succ) (fun i => batch i.succ) (giantSignedChronologicalTail h)
      (giantSignedChronologicalTail_compatible h κ hc)
    let F (i : Fin (n+2)) := giantSignedChronologicalGhostCoefficient ν V visitQ ρ h i
    let J (i : Fin (n+1)) := giantSignedChronologicalEdgeCoefficient ν V κ q ρ θ ζ (fun i => K i (p i).val) h i
    let X := ∏ i : Fin (n+1), F i.succ
    let Y := ∏ i : Fin n, J i.succ
    have hTail : giantSignedTraceWeight giantSignedBoundary rest y t = X*Y :=
      ih (fun i => patterns i.succ) (fun i => C i.succ) (fun i => κ i.succ) (fun i => visitQ i.succ)
        (fun i => ζ i.succ) (fun i => K i.succ) (fun i => p i.succ) (fun i => batch i.succ)
        (giantSignedChronologicalTail h) (giantSignedChronologicalTail_compatible h κ hc) hb
    have hRaw : giantSignedRawEdgeCoefficient ν V (κ 0) q ρ θ (ζ 0) (K 0 (p 0).val) a r = J 0 :=
      giantSignedChronologicalRawMove_coefficient ν V κ q ρ θ ζ (fun i => K i (p i).val) h hc 0
    let b := giantSignedRawEdgeCoefficient ν V (κ 0) q ρ θ (ζ 0) (K 0 (p 0).val) a r
    have hw : giantSignedTraceWeight giantSignedBoundary rest x
        (cast (congrArg (GiantSignedTrace rest) hxy.symm) t) = X*Y :=
      (traceWeight_cast giantSignedBoundary rest hxy t).trans hTail
    change F 0 * ((b*1) * giantSignedTraceWeight giantSignedBoundary rest x
      (cast (congrArg (GiantSignedTrace rest) hxy.symm) t)) = (∏ i, F i) * ∏ i, J i
    change b = J 0 at hRaw
    rw [mul_one,hw,hRaw,Fin.prod_univ_succ F,Fin.prod_univ_succ J]
    change F 0 * (J 0 * (X*Y)) = (F 0*X)*(J 0*Y)
    ac_rfl

end
end ArtinMatthews
