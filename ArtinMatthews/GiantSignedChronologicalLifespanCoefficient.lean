module

public import ArtinMatthews.GiantSignedChronologicalLifespanLocalCoefficient
public import ArtinMatthews.GiantPrimeRowWeight
public import ArtinMatthews.GiantSignedPrimeChronologicalStatusWeight
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

/-! The actual chronological coefficient factors over the chosen prime lifespans. -/

namespace ArtinMatthews

open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq B] [DecidableEq S]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell n : ℕ}
    {C : Fin n → B → Finset (Fin k)} {batch : Fin (n+1) → B → ℕ}
    {A : (g : B) → PB g → Finset (Fin (n+1))}
    (c : ∀ g p, GiantSignedResidueLifespanChoice (A g p))
    (h : GiantSignedChronologicalChoices PS PB ell C batch)
    (offset : Fin (n+1) → ℤ)

/-- The literal old indices, birth orders, and free slots of an actual chronology. -/
structure GiantSignedChronologicalLifespanCoefficientData where
  before : ∀ i g, GiantSignedLifespanMemory (giantSignedGhostVisitBefore (c g) i)
    (giantSignedLifespanResidue (c g) offset i) (giantSignedMemoryGroupEquiv PB (h.state i).2.2 g)
  after : ∀ i g, GiantSignedLifespanMemory (giantSignedGhostVisitAfter (c g) i)
    (giantSignedLifespanResidue (c g) offset i)
    (giantSignedMemoryGroupEquiv PB (giantSignedChronologicalGhostTarget h i) g)
  initialInjective : ∀ g, Function.Injective ((h.state 0).2.1 g)
  initialRange : ∀ g (p : PB g), (0 : Fin (n+1)) ∈ A g p ↔ ∃ j, (h.state 0).2.1 g j = p
  targetInjective : ∀ i g, Function.Injective
    (giantSignedPatternFreeLabels (C i) (giantSignedChronologicalBigTarget h i) g)
  targetRange : ∀ i g (p : PB g),
    (∃ j, giantSignedPatternFreeLabels (C i) (giantSignedChronologicalBigTarget h i) g j = p) ↔
      i.succ ∈ A g p ∧ i.castSucc ∉ A g p
  ghostMatch : ∀ i g, GiantSignedChronologicalLifespanGhostMatch c h i g
  edgeMatch : ∀ i, h.edge i = giantSignedLifespanEdgeChoice c i.castSucc i.succ offset
    (giantSignedChronologicalGhostTarget h i.castSucc) (after i.castSucc)
    (giantSignedPatternFreeLabels (C i) (giantSignedChronologicalBigSource h i))
    (giantSignedPatternFreeLabels (C i) (giantSignedChronologicalBigTarget h i)) (targetInjective i)

/-- The initial big-prime tilt and every literal ghost and memory-edge coefficient. -/
def giantSignedChronologicalPrimeProduct (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (κ : Fin n → ℤ)
    (q : Fin (n+1) → ℝ) (ρ : ℝ) : ℂ :=
  (giantSignedActiveMass ν (h.state 0).2.1 : ℂ) *
    (∏ i, giantSignedChronologicalGhostCoefficient ν V q ρ h i) *
    ∏ i, giantSignedChronologicalEdgeMemoryCoefficient ν V κ ρ h i

/-- One inverse factorial for each actual ordered birth batch. -/
def giantSignedChronologicalBirthFactor (batch : Fin (n+1) → B → ℕ) : ℂ :=
  ∏ i, ∏ g, ((batch i g).factorial : ℂ)⁻¹

private theorem prime_chronology_reindex {I J : Type*} [Fintype I] [Fintype J]
    (initial : (g : B) → PB g → ℂ) (ghost : I → (g : B) → PB g → ℂ)
    (edge : J → (g : B) → PB g → ℂ) (factorial : I → B → ℂ) :
    (∏ g, ∏ p, initial g p) * (∏ i, ∏ g, (∏ p, ghost i g p) / factorial i g) *
        (∏ j, ∏ g, ∏ p, edge j g p) =
      (∏ i, ∏ g, (factorial i g)⁻¹) *
        ∏ g, ∏ p, initial g p * (∏ i, ghost i g p) * ∏ j, edge j g p := by
  have hg : (∏ i, ∏ g, ∏ p, ghost i g p) = ∏ g, ∏ p, ∏ i, ghost i g p := by
    calc
      _ = ∏ g, ∏ i, ∏ p, ghost i g p := Finset.prod_comm
      _ = _ := Finset.prod_congr rfl fun g _ => Finset.prod_comm
  have he : (∏ j, ∏ g, ∏ p, edge j g p) = ∏ g, ∏ p, ∏ j, edge j g p := by
    calc
      _ = ∏ g, ∏ j, ∏ p, edge j g p := Finset.prod_comm
      _ = _ := Finset.prod_congr rfl fun g _ => Finset.prod_comm
  simp only [div_eq_mul_inv, Finset.prod_mul_distrib, hg, he]
  ac_rfl

theorem giantSignedChronologicalPrimeProduct_eq_status (V : B → ℝ) (ρ : ℝ)
    (κ : Fin n → ℤ) (q : Fin (n+1) → ℝ)
    (ha : GiantSignedChronologicalAdmissible κ h)
    (data : GiantSignedChronologicalLifespanCoefficientData c h offset)
    (hw : ∀ g p, giantSignedResidueLifespanWeight p.val offset q (A g p) (c g p) ≠ 0) :
    giantSignedChronologicalPrimeProduct h (fun g p => giantSignedRowBirthAtom (V g) p.val q) V κ q ρ =
      giantSignedChronologicalBirthFactor batch *
        ∏ g, ∏ p : PB g, giantSignedPrimeChronologicalStatusProduct (c g) (V g) ρ offset q p := by
  unfold giantSignedChronologicalPrimeProduct
  rw [giantSignedLifespanInitialMass_eq V q (h.state 0).2.1 data.initialInjective data.initialRange]
  have hg (i : Fin (n+1)) := giantSignedChronologicalGhostCoefficient_eq_lifespan c h V ρ offset q i
    (data.before i) (data.ghostMatch i) hw
  have he (i : Fin n) := giantSignedChronologicalEdgeMemoryCoefficient_eq_lifespan c h V ρ κ offset q i ha
    (data.before i.succ) (data.after i.castSucc) (data.targetInjective i) (data.targetRange i) (data.edgeMatch i)
  simp_rw [hg, he]
  exact prime_chronology_reindex
    (fun g (p : PB g) => if (0 : Fin (n+1)) ∈ A g p then (giantSignedRowBirthAtom (V g) p.val q : ℂ) else 1)
    (fun i g p => giantSignedPrimeVisitGhostFactor (c g) (V g) ρ offset q i p)
    (fun i : Fin n => fun g p => giantSignedLifespanEdgePrimeFactor c (V g) ρ offset q i.castSucc i.succ g p)
    (fun i g => ((batch i g).factorial : ℂ))

theorem giantSignedChronologicalPrimeProduct_eq_rowWeight (V : B → ℝ) (ρ : ℝ)
    (κ : Fin n → ℤ) (q : Fin (n+1) → ℝ)
    (ha : GiantSignedChronologicalAdmissible κ h)
    (data : GiantSignedChronologicalLifespanCoefficientData c h offset)
    (hw : ∀ g p, giantSignedResidueLifespanWeight p.val offset q (A g p) (c g p) ≠ 0) :
    giantSignedChronologicalPrimeProduct h (fun g p => giantSignedRowBirthAtom (V g) p.val q) V κ q ρ =
      giantSignedChronologicalBirthFactor batch *
        ∏ g, ∏ p : PB g, (giantSignedPrimeRowWeight (V g) ρ p.val offset q (A g p) (c g p) : ℂ) := by
  rw [giantSignedChronologicalPrimeProduct_eq_status c h offset V ρ κ q ha data hw]
  simp_rw [giantSignedPrimeChronologicalStatusProduct_eq_rowWeight _ _ _ _ _ _ (hw _ _)]

theorem giantSignedChronologicalPrimeProduct_eq_lifespan (V : B → ℝ) (ρ : ℝ)
    (κ : Fin n → ℤ) (q : Fin (n+1) → ℝ)
    (ha : GiantSignedChronologicalAdmissible κ h)
    (data : GiantSignedChronologicalLifespanCoefficientData c h offset)
    (hw : ∀ g p, giantSignedResidueLifespanWeight p.val offset q (A g p) (c g p) ≠ 0)
    (hV : ∀ g, V g ≠ 0) (hρ : ρ ≠ 0) (hb : ∀ g (p : PB g), giantSignedPrimeResidueBaseline p.val q ≠ 0) :
    giantSignedChronologicalPrimeProduct h (fun g p => giantSignedRowBirthAtom (V g) p.val q) V κ q ρ =
      giantSignedChronologicalBirthFactor batch * ∏ g, ∏ p : PB g,
        ((((V g)⁻¹) ^ giantSignedActiveRunCount (A g p) *
          (giantSignedResidueLifespanWeight p.val offset q (A g p) (c g p) /
            giantSignedPrimeResidueBaseline p.val q) : ℝ) : ℂ) := by
  rw [giantSignedChronologicalPrimeProduct_eq_status c h offset V ρ κ q ha data hw]
  congr 1
  apply Finset.prod_congr rfl
  intro g _
  exact Finset.prod_congr rfl fun p _ =>
    giantSignedPrimeChronologicalStatusProduct_eq (c g) (V g) ρ (hV g) hρ offset q p (hw g p) (hb g p)

end
end ArtinMatthews
