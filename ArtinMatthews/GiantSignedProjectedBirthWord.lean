module

public import ArtinMatthews.GiantSignedGhostBirthApply
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

/-! The projected chronological word with local performed-birth phases.
The original source and target measures and both projections are retained. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
universe u

variable {S B I : Type u} [Fintype S] [DecidableEq S] [Fintype B] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell : ℕ}
    [Fintype (GiantTwoSidedResidueState PS (k+ell))]

def giantSignedProjectedBirthChronologicalWord (H : ℕ)
    (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (q ρ θ : ℝ)
    (f : GiantSignedState PS PB (k+ell) → ℂ) :
    (n : ℕ) → (patterns : Fin n → Finset I) →
      (C : Fin n → I → B → Finset (Fin k)) →
      (κ : Fin n → ℤ) → (visitQ : Fin (n+1) → ℝ) → (ζ : Fin n → ℝ) →
      ((i : Fin n) → (p : I) → GiantTwoSidedPatternCoefficient PB (C i p) ell) →
      ((i : Fin n) → (p : I) → (s : GiantSignedState PS PB (k+ell)) →
        GiantSignedRawEdgeMove PS PB ell (C i p) s.2.2 → ℂ) →
      (Fin (n+1) → GiantSignedGhostBirthMultiplier PB) →
      GiantSignedState PS PB (k+ell) → ℂ
  | 0, _, _, _, visitQ, _, _, _, φ =>
      giantSignedProjectedBirthVisit H ν V (visitQ 0) ρ (φ 0) f
  | n+1, patterns, C, κ, visitQ, ζ, K, η, φ =>
      giantSignedProjectedBirthVisit H ν V (visitQ 0) ρ (φ 0)
        (giantSignedProjectedRawEdgeFamilyApply H ν V (patterns 0) (C 0) (κ 0)
          q ρ θ (ζ 0) (K 0) (η 0)
          (giantSignedProjectedBirthChronologicalWord H ν V q ρ θ f n
            (fun i => patterns i.succ) (fun i => C i.succ) (fun i => κ i.succ)
            (fun i => visitQ i.succ) (fun i => ζ i.succ) (fun i => K i.succ)
            (fun i => η i.succ) (fun i => φ i.succ)))

def giantSignedProjectedBirthBoundaryPairing (H : ℕ)
    (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (q ρ θ : ℝ)
    (n : ℕ) (patterns : Fin n → Finset I)
    (C : Fin n → I → B → Finset (Fin k)) (κ : Fin n → ℤ)
    (visitQ : Fin (n+1) → ℝ) (ζ : Fin n → ℝ)
    (K : (i : Fin n) → (p : I) → GiantTwoSidedPatternCoefficient PB (C i p) ell)
    (η : (i : Fin n) → (p : I) → (s : GiantSignedState PS PB (k+ell)) →
      GiantSignedRawEdgeMove PS PB ell (C i p) s.2.2 → ℂ)
    (φ : Fin (n+1) → GiantSignedGhostBirthMultiplier PB)
    (φ₀ : MarkedPhysicalMarking PB (k+ell) → ℂ) : ℂ :=
  ∑ y : GiantTwoSidedResidueState PS (k+ell), ∑ a : MarkedPhysicalMarking PB (k+ell),
    ((giantTwoSidedResidueHaarStateMass PS (k+ell) * giantSignedActiveMass ν a : ℝ) : ℂ) *
      φ₀ a * giantSignedProjectedBirthChronologicalWord H ν V q ρ θ giantSignedBoundary
        n patterns C κ visitQ ζ K η φ (y,a,giantSignedEmptyMemory PB)

theorem giantSignedProjectedRawEdgeFamilyApply_multiplier_congr (H : ℕ)
    (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (patterns : Finset I)
    (C : I → B → Finset (Fin k)) (κ : ℤ) (q ρ θ ζ : ℝ)
    (K : ∀ p, GiantTwoSidedPatternCoefficient PB (C p) ell)
    (η₁ η₂ : (p : I) → (s : GiantSignedState PS PB (k+ell)) →
      GiantSignedRawEdgeMove PS PB ell (C p) s.2.2 → ℂ)
    (hη : ∀ p ∈ patterns, ∀ s r, η₁ p s r = η₂ p s r)
    (f : GiantSignedState PS PB (k+ell) → ℂ) :
    giantSignedProjectedRawEdgeFamilyApply H ν V patterns C κ q ρ θ ζ K η₁ f =
      giantSignedProjectedRawEdgeFamilyApply H ν V patterns C κ q ρ θ ζ K η₂ f := by
  unfold giantSignedProjectedRawEdgeFamilyApply
  apply congrArg (giantSignedStateMemoryCutoff H)
  funext s
  unfold giantSignedRawEdgeFamilyApply
  apply Finset.sum_congr rfl
  intro p hp
  unfold giantSignedRawEdgeApply
  apply Finset.sum_congr rfl
  intro r _
  rw [hη p hp s r]

end
end ArtinMatthews
