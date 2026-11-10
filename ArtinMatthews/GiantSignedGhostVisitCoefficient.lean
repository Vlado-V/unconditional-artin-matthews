module

public import ArtinMatthews.GiantSignedGhostVisitReconstruction
public import ArtinMatthews.GiantSignedGhostMoves
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
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

/-! The exact coefficient of the reconstructed ordered ghost visit. -/

namespace ArtinMatthews

open scoped BigOperators

noncomputable section

variable {P : Finset ℕ} {n : ℕ} {A : (p : P) → Finset (Fin n)}
    (c : (p : P) → GiantSignedResidueLifespanChoice (A p))

def giantSignedGhostVisitRetainedZero (offset : Fin n → ℤ) (i : Fin n) (p : P) : Prop :=
  giantSignedPrimePendingBefore (c p) i ∧ ¬giantSignedPrimeGhostDeathAt (c p) i ∧
    giantSignedLifespanResidue c offset i p = 0

def giantSignedGhostVisitPrimeFactor (offset : Fin n → ℤ) (i : Fin n)
    (ν : P → ℝ) (hold birth death : ℂ) (p : P) : ℂ := by
  classical
  exact (if giantSignedPrimeGhostDeathAt (c p) i then death else 1) *
    (if giantSignedGhostVisitRetainedZero c offset i p then hold else 1) *
    (if giantSignedPrimeGhostBirthAt (c p) i then birth * (ν p : ℂ) else 1)

def giantSignedGhostVisitMove (i : Fin n) (m : GiantSignedGroupMemory P)
    (order : Fin (giantSignedGhostVisitBorn c i).card ≃ ↥(giantSignedGhostVisitBorn c i)) :
    GiantSignedGhostMoves m :=
  ⟨giantSignedGhostVisitDeleted c i m, (giantSignedGhostVisitBorn c i).card,
    giantSignedGhostVisitBornLabels order⟩

private theorem anchored_filter_card {pending : Finset P} {anchor : (p : P) → ZMod p.val}
    {m : GiantSignedGroupMemory P} (h : GiantSignedLifespanMemory pending anchor m)
    (r : P → Prop) [DecidablePred r] (hr : ∀ p, r p → p ∈ pending) :
    (Finset.univ.filter (fun j : Fin m.1 => r (m.2 j).1)).card =
      (Finset.univ.filter r).card := by
  let e : Fin m.1 ↪ P := ⟨fun j => (m.2 j).1, h.prime_injective⟩
  have he : (Finset.univ.filter (fun j : Fin m.1 => r (m.2 j).1)).map e =
      Finset.univ.filter r := by
    ext p
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact hj
    · intro hp
      let p' : ↥pending := ⟨p, hr p hp⟩
      let j := h.index p'
      have hj : e j = p := h.index_prime p'
      exact ⟨j, (congrArg r hj).mpr hp, hj⟩
  rw [← he, Finset.card_map]

theorem giantSignedGhostVisitMoveCoefficient_eq (offset : Fin n → ℤ) (q : Fin n → ℝ)
    (i : Fin n) (ν : P → ℝ) (hold birth death : ℂ) (m : GiantSignedGroupMemory P)
    (h : GiantSignedLifespanMemory (giantSignedGhostVisitBefore c i)
      (giantSignedLifespanResidue c offset i) m)
    (hw : ∀ p : P, giantSignedResidueLifespanWeight p.val offset q (A p) (c p) ≠ 0)
    (order : Fin (giantSignedGhostVisitBorn c i).card ≃ ↥(giantSignedGhostVisitBorn c i)) :
    giantSignedGhostMoveCoefficient ν hold birth death m (giantSignedGhostVisitMove c i m order) =
      (∏ p : P, giantSignedGhostVisitPrimeFactor c offset i ν hold birth death p) /
        ((giantSignedGhostVisitBorn c i).card.factorial : ℂ) := by
  classical
  let deleted := giantSignedGhostVisitDeleted c i m
  let dead := Finset.univ.filter (fun p : P => giantSignedPrimeGhostDeathAt (c p) i)
  let held := Finset.univ.filter (giantSignedGhostVisitRetainedZero c offset i)
  let born := giantSignedGhostVisitBorn c i
  have hsub : deleted ⊆ giantSignedGhostZeroIndices m :=
    giantSignedGhostVisit_deleted_subset_zeros c offset q i m h hw
  have hdead : deleted.card = dead.card := by
    simpa only [deleted, dead, giantSignedGhostVisitDeleted] using
      anchored_filter_card h (fun p => giantSignedPrimeGhostDeathAt (c p) i) (fun p hp =>
        (mem_giantSignedGhostVisitBefore c i p).mpr
          (giantSignedPrimeGhostDeathAt_pendingBefore (c p) i hp))
  have hHeldIndices : giantSignedGhostZeroIndices m \ deleted =
      Finset.univ.filter (fun j : Fin m.1 => giantSignedGhostVisitRetainedZero c offset i (m.2 j).1) := by
    apply Finset.ext
    intro j
    have hp := (mem_giantSignedGhostVisitBefore c i _).mp (h.prime_mem j)
    have hz : ((m.2 j).2 = 0) = (giantSignedLifespanResidue c offset i (m.2 j).1 = 0) :=
      congrArg (fun z : GiantSignedParticle P => z.2 = 0) (h.particle_anchor j)
    have hzeroIndex : j ∈ giantSignedGhostZeroIndices m ↔ (m.2 j).2 = 0 := by
      change j ∈ Finset.univ.filter (fun k : Fin m.1 => (m.2 k).2 = 0) ↔ _
      exact ⟨fun hj => (Finset.mem_filter.mp hj).2,
        fun hj => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
    have hdel : j ∈ deleted ↔ giantSignedPrimeGhostDeathAt (c (m.2 j).1) i :=
      mem_giantSignedGhostVisitDeleted c i m j
    rw [Finset.mem_sdiff, hzeroIndex, hdel, Finset.mem_filter, hz]
    simp only [Finset.mem_univ, true_and, giantSignedGhostVisitRetainedZero]
    exact ⟨fun he => ⟨hp, he.2, he.1⟩, fun he => ⟨he.2.2, he.2.1⟩⟩
  have hheld : (giantSignedGhostZeroIndices m).card - deleted.card = held.card := by
    rw [← Finset.card_sdiff_of_subset hsub, hHeldIndices]
    exact anchored_filter_card h (giantSignedGhostVisitRetainedZero c offset i) (fun p hp =>
      (mem_giantSignedGhostVisitBefore c i p).mpr hp.1)
  have hborn : (∏ j, (ν (giantSignedGhostVisitBornLabels order j) : ℂ)) =
      ∏ p ∈ born, (ν p : ℂ) := by
    calc
      _ = ∏ p : ↥born, (ν p.val : ℂ) := order.prod_comp _
      _ = _ := Finset.prod_coe_sort (s := born) (f := fun p : P => (ν p : ℂ))
  have hprod : (∏ p : P, giantSignedGhostVisitPrimeFactor c offset i ν hold birth death p) =
      death ^ dead.card * hold ^ held.card * (birth ^ born.card) * ∏ p ∈ born, (ν p : ℂ) := by
    simp only [giantSignedGhostVisitPrimeFactor, Finset.prod_mul_distrib, ← Finset.prod_filter,
      Finset.prod_const, dead, held, born, giantSignedGhostVisitBorn]
    ring
  have hraw :
      giantSignedGhostMoveCoefficient ν hold birth death m (giantSignedGhostVisitMove c i m order) =
        death ^ deleted.card * hold ^ ((giantSignedGhostZeroIndices m).card - deleted.card) *
          (birth ^ born.card / (born.card.factorial : ℂ)) *
            ∏ j, (ν (giantSignedGhostVisitBornLabels order j) : ℂ) := by
    unfold giantSignedGhostMoveCoefficient
    split_ifs with hguard
    · rfl
    · exact (hguard hsub).elim
  rw [hraw, hheld, hdead, hborn, hprod]
  change _ = _ / (born.card.factorial : ℂ)
  ring

theorem giantSignedGhostVisitMoveCoefficient_sum_birth_orders (offset : Fin n → ℤ) (q : Fin n → ℝ)
    (i : Fin n) (ν : P → ℝ) (hold birth death : ℂ) (m : GiantSignedGroupMemory P)
    (h : GiantSignedLifespanMemory (giantSignedGhostVisitBefore c i)
      (giantSignedLifespanResidue c offset i) m)
    (hw : ∀ p : P, giantSignedResidueLifespanWeight p.val offset q (A p) (c p) ≠ 0) :
    (∑ order : Fin (giantSignedGhostVisitBorn c i).card ≃ ↥(giantSignedGhostVisitBorn c i),
      giantSignedGhostMoveCoefficient ν hold birth death m (giantSignedGhostVisitMove c i m order)) =
      ∏ p : P, giantSignedGhostVisitPrimeFactor c offset i ν hold birth death p := by
  classical
  simp_rw [giantSignedGhostVisitMoveCoefficient_eq c offset q i ν hold birth death m h hw]
  rw [Finset.sum_const, Finset.card_univ, giantSignedGhostVisitBirthOrder_card, nsmul_eq_mul]
  have hfac : ((giantSignedGhostVisitBorn c i).card.factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (giantSignedGhostVisitBorn c i).card
  field_simp [hfac]

end

end ArtinMatthews
