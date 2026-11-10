module

public import ArtinMatthews.GiantSignedLifespanEdgeCoefficient
public import ArtinMatthews.GiantSignedChronologicalSupport
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

/-! The original chronological ghost and memory-edge coefficients use
exactly the prime products of a matched family of lifespans. -/

namespace ArtinMatthews

open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell n : ℕ}
    {C : Fin n → B → Finset (Fin k)} {batch : Fin (n+1) → B → ℕ}
    {A : (g : B) → PB g → Finset (Fin (n+1))}
    (c : ∀ g p, GiantSignedResidueLifespanChoice (A g p))
    (h : GiantSignedChronologicalChoices PS PB ell C batch)

def GiantSignedChronologicalLifespanGhostMatch (i : Fin (n+1)) (g : B) : Prop :=
  ∃ order : Fin (giantSignedGhostVisitBorn (c g) i).card ≃ ↥(giantSignedGhostVisitBorn (c g) i),
    giantSignedFixedGhostMove (h.state i).2.2 (batch i) (h.deleted i) (h.born i) g =
      giantSignedGhostVisitMove (c g) i (giantSignedMemoryGroupEquiv PB (h.state i).2.2 g) order

omit [DecidableEq B] in
theorem giantSignedChronologicalGhostCoefficient_eq_lifespan (V : B → ℝ) (ρ : ℝ)
    (offset : Fin (n+1) → ℤ) (q : Fin (n+1) → ℝ) (i : Fin (n+1))
    (hbefore : ∀ g, GiantSignedLifespanMemory (giantSignedGhostVisitBefore (c g) i)
      (giantSignedLifespanResidue (c g) offset i) (giantSignedMemoryGroupEquiv PB (h.state i).2.2 g))
    (hghost : ∀ g, GiantSignedChronologicalLifespanGhostMatch c h i g)
    (hw : ∀ g p, giantSignedResidueLifespanWeight p.val offset q (A g p) (c g p) ≠ 0) :
    giantSignedChronologicalGhostCoefficient (fun g p => giantSignedRowBirthAtom (V g) p.val q) V q ρ h i =
      ∏ g, (∏ p : PB g, giantSignedPrimeVisitGhostFactor (c g) (V g) ρ offset q i p) /
        ((batch i g).factorial : ℂ) := by
  unfold giantSignedChronologicalGhostCoefficient giantSignedGhostMemoryMoveCoefficient
    giantSignedGhostProductMoveCoefficient
  apply Finset.prod_congr rfl
  intro g _
  obtain ⟨order, he⟩ := hghost g
  let m := giantSignedMemoryGroupEquiv PB (h.state i).2.2 g
  have hbatch : batch i g = (giantSignedGhostVisitBorn (c g) i).card :=
    congrArg (fun move : GiantSignedGhostMoves m => move.2.1) he
  have hcoeff := giantSignedGhostVisitMoveCoefficient_eq (c g) offset q i
    (fun p => giantSignedRowBirthAtom (V g) p.val q) (giantSignedRowA (q i) ρ : ℂ)
    (giantSignedRowC (q i) (V g) ρ : ℂ) (giantSignedRowD (q i) ρ : ℂ) m (hbefore g) (hw g) order
  rw [he]
  refine hcoeff.trans ?_
  simp only [giantSignedPrimeVisitGhostFactor, hbatch]

variable [DecidableEq S]

theorem giantSignedChronologicalEdgeMemoryCoefficient_eq_lifespan (V : B → ℝ) (ρ : ℝ)
    (κ : Fin n → ℤ) (offset : Fin (n+1) → ℤ) (q : Fin (n+1) → ℝ) (i : Fin n)
    (ha : GiantSignedChronologicalAdmissible κ h)
    (hbefore : ∀ g, GiantSignedLifespanMemory (giantSignedGhostVisitBefore (c g) i.succ)
      (giantSignedLifespanResidue (c g) offset i.succ)
      (giantSignedMemoryGroupEquiv PB (h.state i.succ).2.2 g))
    (hafter : ∀ g, GiantSignedLifespanMemory (giantSignedGhostVisitAfter (c g) i.castSucc)
      (giantSignedLifespanResidue (c g) offset i.castSucc)
      (giantSignedMemoryGroupEquiv PB (giantSignedChronologicalGhostTarget h i.castSucc) g))
    (htarget : ∀ g, Function.Injective
      (giantSignedPatternFreeLabels (C i) (giantSignedChronologicalBigTarget h i) g))
    (hrange : ∀ g (p : PB g), (∃ j, giantSignedPatternFreeLabels (C i)
        (giantSignedChronologicalBigTarget h i) g j = p) ↔ i.succ ∈ A g p ∧ i.castSucc ∉ A g p)
    (hedge : h.edge i = giantSignedLifespanEdgeChoice c i.castSucc i.succ offset
      (giantSignedChronologicalGhostTarget h i.castSucc) hafter
      (giantSignedPatternFreeLabels (C i) (giantSignedChronologicalBigSource h i))
      (giantSignedPatternFreeLabels (C i) (giantSignedChronologicalBigTarget h i)) htarget) :
    giantSignedChronologicalEdgeMemoryCoefficient (fun g p => giantSignedRowBirthAtom (V g) p.val q)
      V κ ρ h i = ∏ g, ∏ p : PB g, giantSignedLifespanEdgePrimeFactor c (V g) ρ offset q
        i.castSucc i.succ g p := by
  let m := giantSignedChronologicalGhostTarget h i.castSucc
  let source := giantSignedPatternFreeLabels (C i) (giantSignedChronologicalBigSource h i)
  let target := giantSignedPatternFreeLabels (C i) (giantSignedChronologicalBigTarget h i)
  let choice := giantSignedLifespanEdgeChoice c i.castSucc i.succ offset m hafter source target htarget
  let D := giantSignedChronologicalProduct h i
  let d := κ i * (D : ℤ)
  have hp : GiantSignedEdgeHits d m target choice ∧ GiantSignedEdgePromotionBan D choice.2.1 target := by
    rw [← show h.edge i = choice from hedge]
    exact ha.promotion i
  have hm : (h.state i.succ).2.2 = giantSignedEdgeTarget d m source choice := by
    rw [← show h.edge i = choice from hedge]
    exact (ha.compatible i).2.2.2.1
  have hout (g : B) : GiantSignedLifespanMemory (giantSignedGhostVisitBefore (c g) i.succ)
      (giantSignedLifespanResidue (c g) offset i.succ)
      (giantSignedMemoryGroupEquiv PB (giantSignedEdgeTarget d m source choice) g) := by
    rw [← hm]
    exact hbefore g
  unfold giantSignedChronologicalEdgeMemoryCoefficient
  rw [hedge]
  exact giantSignedLifespanEdgeMoveCoefficient_eq c V ρ offset q i.castSucc i.succ rfl d D
    m source target htarget hrange hafter hp.1 hp.2 hout

end
end ArtinMatthews
