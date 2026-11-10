module

public import ArtinMatthews.GiantSignedLifespanEdgeTarget
public import ArtinMatthews.GiantSignedChronologicalChoices
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

/-! Ordered before- and after-visit memories for fixed lifespan terms.
The recursion uses the original ghost and edge targets, so an ordered birth
batch determines every subsequent pending index without a degree cutoff. -/

namespace ArtinMatthews
noncomputable section

variable {B : Type*} {P : B → Finset ℕ} {n : ℕ}
    {A : ∀ g, P g → Finset (Fin (n+1))}

structure GiantSignedLifespanScheduleData
    (c : ∀ g p, GiantSignedResidueLifespanChoice (A g p))
    (offset : Fin (n+1) → ℤ) (q : Fin (n+1) → ℝ) (t : Fin n → B → ℕ) where
  increment : Fin n → ℤ
  offset_step : ∀ i, offset i.succ = offset i.castSucc + increment i
  source : ∀ i, GiantSignedPrimeTuple P (t i)
  target : ∀ i, GiantSignedPrimeTuple P (t i)
  source_injective : ∀ i g, Function.Injective (source i g)
  target_injective : ∀ i g, Function.Injective (target i g)
  source_cover : ∀ i g p, i.castSucc ∈ A g p → i.succ ∉ A g p → ∃ j, source i g j = p
  target_cover : ∀ i g p, i.succ ∈ A g p → i.castSucc ∉ A g p → ∃ j, target i g j = p
  weight_ne_zero : ∀ g p, giantSignedResidueLifespanWeight p.val offset q (A g p) (c g p) ≠ 0
  birthOrder : ∀ v g, Fin (giantSignedGhostVisitBorn (c g) v).card ≃
    ↥(giantSignedGhostVisitBorn (c g) v)

namespace GiantSignedLifespanScheduleData

variable {c : ∀ g p, GiantSignedResidueLifespanChoice (A g p)}
    {offset : Fin (n+1) → ℤ} {q : Fin (n+1) → ℝ} {t : Fin n → B → ℕ}

abbrev Before (v : Fin (n+1)) :=
  Σ m : GiantSignedMemory P, ∀ g,
    GiantSignedLifespanMemory (giantSignedGhostVisitBefore (c g) v)
      (giantSignedLifespanResidue (c g) offset v) (giantSignedMemoryGroupEquiv P m g)

def first : Before (c := c) (offset := offset) 0 := by
  refine ⟨giantSignedEmptyMemory P, fun g => ?_⟩
  let _ : IsEmpty ↥(giantSignedGhostVisitBefore (c g) 0) :=
    ⟨fun p => giantSignedPrimePendingBefore_first (c g p.val)
      ((mem_giantSignedGhostVisitBefore (c g) 0 p.val).mp p.property)⟩
  exact ⟨Equiv.equivOfIsEmpty (Fin 0) ↥(giantSignedGhostVisitBefore (c g) 0), fun j => Fin.elim0 j⟩

variable (data : GiantSignedLifespanScheduleData c offset q t)

def batch (_data : GiantSignedLifespanScheduleData c offset q t) (v : Fin (n+1)) (g : B) : ℕ :=
  (giantSignedGhostVisitBorn (c g) v).card

def born (v : Fin (n+1)) (g : B) : Fin (data.batch v g) → P g :=
  giantSignedGhostVisitBornLabels (data.birthOrder v g)

def deleted (v : Fin (n+1)) (m : Before (c := c) (offset := offset) v) (g : B) :
    Finset (Fin (m.1.1 g)) :=
  giantSignedGhostVisitDeleted (c g) v (giantSignedMemoryGroupEquiv P m.1 g)

def after (v : Fin (n+1)) (m : Before (c := c) (offset := offset) v) : GiantSignedMemory P :=
  giantSignedFixedGhostTarget m.1 (data.batch v) (deleted v m) (data.born v)

def after_certificate (v : Fin (n+1)) (m : Before (c := c) (offset := offset) v) (g : B) :
    GiantSignedLifespanMemory (giantSignedGhostVisitAfter (c g) v)
      (giantSignedLifespanResidue (c g) offset v) (giantSignedMemoryGroupEquiv P (data.after v m) g) :=
  giantSignedGhostVisitTarget_memory (c g) offset v _ (m.2 g) (data.birthOrder v g)

def edge (i : Fin n) (m : Before (c := c) (offset := offset) i.castSucc) :
    GiantSignedEdgeChoice (t i) (data.after i.castSucc m).1 :=
  giantSignedLifespanEdgeChoice c i.castSucc i.succ offset (data.after i.castSucc m)
    (data.after_certificate i.castSucc m) (data.source i) (data.target i) (data.target_injective i)

def advance (i : Fin n) (m : Before (c := c) (offset := offset) i.castSucc) :
    Before (c := c) (offset := offset) i.succ :=
  ⟨giantSignedEdgeTarget (data.increment i) (data.after i.castSucc m) (data.source i) (data.edge i m),
    giantSignedLifespanEdgeTarget_memory c i.castSucc i.succ offset (data.after i.castSucc m)
      (data.after_certificate i.castSucc m) (data.source i) (data.target i) (data.target_injective i)
      q (data.increment i) (data.offset_step i) rfl data.weight_ne_zero
      (data.source_injective i) (data.source_cover i) (data.target_cover i)⟩

def memory (v : Fin (n+1)) : Before (c := c) (offset := offset) v :=
  Fin.induction first data.advance v

theorem memory_zero : (data.memory 0).1 = giantSignedEmptyMemory P := rfl

theorem memory_succ (i : Fin n) :
    data.memory i.succ = data.advance i (data.memory i.castSucc) := by
  unfold memory
  rw [Fin.induction_succ]

theorem deleted_subset_zeros (v : Fin (n+1)) (g : B) :
    deleted v (data.memory v) g ⊆ giantSignedGhostZeroIndices
      (giantSignedMemoryGroupEquiv P (data.memory v).1 g) :=
  giantSignedGhostVisit_deleted_subset_zeros (c g) offset q v _ ((data.memory v).2 g)
    (data.weight_ne_zero g)

theorem edge_hits (i : Fin n) :
    GiantSignedEdgeHits (data.increment i) (data.after i.castSucc (data.memory i.castSucc))
      (data.target i) (data.edge i (data.memory i.castSucc)) :=
  giantSignedLifespanEdgeChoice_hits c i.castSucc i.succ offset
    (data.after i.castSucc (data.memory i.castSucc)) (data.after_certificate i.castSucc (data.memory i.castSucc))
    (data.source i) (data.target i) (data.target_injective i) q (data.increment i)
    (data.offset_step i) data.weight_ne_zero

private theorem memory_eq_empty_of_degree (m : GiantSignedMemory P) (h : ∀ g, m.1 g = 0) :
    m = giantSignedEmptyMemory P := by
  cases m with
  | mk d particles =>
    have hd : d = fun _ => 0 := funext h
    subst d
    have hp : particles = fun _ j => Fin.elim0 j := by
      funext g j
      exact Fin.elim0 j
    rw [hp]
    rfl

theorem after_last : data.after (Fin.last n) (data.memory (Fin.last n)) = giantSignedEmptyMemory P := by
  apply memory_eq_empty_of_degree
  intro g
  let m := data.after (Fin.last n) (data.memory (Fin.last n))
  change m.1 g = 0
  by_contra h
  let j : Fin (m.1 g) := ⟨0, Nat.pos_of_ne_zero h⟩
  let p := (data.after_certificate (Fin.last n) (data.memory (Fin.last n)) g).enumeration j
  exact giantSignedPrimePendingAfter_last (c g p.val)
    ((mem_giantSignedGhostVisitAfter (c g) (Fin.last n) p.val).mp p.property)

end GiantSignedLifespanScheduleData
end
end ArtinMatthews
