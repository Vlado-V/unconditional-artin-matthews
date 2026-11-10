module

public import ArtinMatthews.MarkedMinorArcRawEdgeState
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

/-! Actual store/promote choices are invariant under reindexing old
pending particles. Fresh labels remain singletons in promoted groups. -/
noncomputable section
open scoped BigOperators
namespace ArtinMatthews
set_option backward.isDefEq.respectTransparency false
-- The pinned dependent fresh-label matchers are instance-reducible in
-- Lean 4.35; expose their definitional Option eliminators locally below.
set_option linter.auxLemma false

theorem markedRawEdgeFreshRec_none {X : Type} {k : ℕ} (x : X)
    (p : Option (Fin k)) (h : p=none) :
    HEq (Option.rec (motive := fun p : Option (Fin k) => Option.casesOn p X (fun _ => PUnit))
      x (fun _ => PUnit.unit) p) x := by
  subst p
  rfl

def markedRawEdgeFreshReindex {X : Type*} {k k' : ℕ} (e : Fin k' ≃ Fin k)
    (p : Option (Fin k)) : (match p with | none => X | some _ => PUnit) →
      (match p.map e.symm with | none => X | some _ => PUnit) := by
  cases p <;> exact id

def markedRawEdgeFreshTarget {X : Type*} {k : ℕ} (a : Fin k → X)
    (p : Option (Fin k)) (u : match p with | none => X | some _ => PUnit) : X :=
  match (generalizing := false) h : p with
  | none => by simpa only [h] using u
  | some i => a i

theorem markedRawEdgeFreshTarget_injective {X : Type*} {k : ℕ}
    (a : Fin k → X) (p : Option (Fin k)) : Function.Injective (markedRawEdgeFreshTarget a p) := by
  cases p with
  | none => exact fun _ _ h => h
  | some i => exact fun _ _ _ => Subsingleton.elim _ _

theorem markedRawEdgeFreshTarget_reindex {X : Type*} {k k' : ℕ} (e : Fin k' ≃ Fin k)
    (a : Fin k → X) (a' : Fin k' → X) (ha : ∀ i, a' i=a (e i))
    (p : Option (Fin k)) (u : match p with | none => X | some _ => PUnit) :
    markedRawEdgeFreshTarget a' (p.map e.symm) (markedRawEdgeFreshReindex (X := X) e p u)=
      markedRawEdgeFreshTarget a p u := by
  cases p with
  | none => rfl
  | some i => simpa only [markedRawEdgeFreshTarget, Option.map_some, Equiv.apply_symm_apply] using ha (e.symm i)

theorem markedRawEdgeReindex_survivor_card {k k' : ℕ} (e : Fin k' ≃ Fin k)
    (p : Option (Fin k)) :
    (Finset.univ \ (p.map e.symm).toFinset).card=(Finset.univ \ p.toFinset).card := by
  have hk : k'=k := by simpa only [Fintype.card_fin] using Fintype.card_congr e
  cases p <;> simp [Finset.card_sdiff, hk]

/-- This transport changes only old pending indices; source position and
active lists play no part in the definition of an eligible edge choice. -/
abbrev markedRawEdgeChoiceReindex {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s s' : MarkedRawState P (pads+1) B Z)
    (e : (j : J) → Fin (s'.2.2.1.1 j : ℕ) ≃ Fin (s.2.2.1.1 j : ℕ))
    (he : ∀ j i, s'.2.2.2 j i=s.2.2.2 j (e j i))
    (c : MarkedRawEdgeChoice hZ s) : MarkedRawEdgeChoice hZ s' where
  target := c.target
  store := c.store
  promotions := fun j => (c.promotions j).map (e j).symm
  fresh := fun j => by
    unfold MarkedRawEdgeFreshLabels.match_1
    exact Option.rec
      (motive := fun p : Option (Fin (s'.2.2.1.1 j : ℕ)) =>
        Option.casesOn p ↥(P j) (fun _ => PUnit))
      (markedRawEdgeTargetLast s.2.2 c.promotions c.fresh j)
      (fun _ => PUnit.unit) ((c.promotions j).map (e j).symm)
  promotion_hits := by
    intro j k hk
    obtain ⟨i,hi,hik⟩ := Option.map_eq_some_iff.mp hk
    subst k
    rw [he, Equiv.apply_symm_apply]
    exact c.promotion_hits j i hi
  memory_bound := by
    change (∑ j, ((Finset.univ \ ((c.promotions j).map (e j).symm).toFinset).card+
      (if c.store j then 1 else 0))) ≤ B
    simpa only [markedRawEdgeReindex_survivor_card, markedRawGhostSurvivors,
      markedRawEdgePromotionDeletion] using c.memory_bound

theorem markedRawEdgeChoiceReindex_targetLast {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s s' : MarkedRawState P (pads+1) B Z)
    (e : (j : J) → Fin (s'.2.2.1.1 j : ℕ) ≃ Fin (s.2.2.1.1 j : ℕ))
    (he : ∀ j i, s'.2.2.2 j i=s.2.2.2 j (e j i)) (c : MarkedRawEdgeChoice hZ s) :
    markedRawEdgeTargetLast s'.2.2 (markedRawEdgeChoiceReindex hZ s s' e he c).promotions
      (markedRawEdgeChoiceReindex hZ s s' e he c).fresh =
      markedRawEdgeTargetLast s.2.2 c.promotions c.fresh := by
  funext j
  unfold markedRawEdgeTargetLast
  split
  · rename_i hn
    apply eq_of_heq
    apply HEq.trans (cast_heq _ _)
    refine HEq.trans ?_ (markedRawEdgeFreshRec_none
      (markedRawEdgeTargetLast s.2.2 c.promotions c.fresh j)
      ((c.promotions j).map (e j).symm) hn)
    dsimp only [markedRawEdgeChoiceReindex]
    unfold MarkedRawEdgeFreshLabels.match_1
    rfl
  · rename_i k hk
    change (c.promotions j).map (e j).symm=some k at hk
    obtain ⟨i,hi,hik⟩ := Option.map_eq_some_iff.mp hk
    subst k
    rw [he, Equiv.apply_symm_apply]
    exact (markedRawEdgeTargetLast_promoted s.2.2 c.promotions c.fresh j i hi).symm

/-- Equality of actual promotion indices and target labels determines
the dependent fresh-label choices, since promoted groups are singletons. -/
theorem markedRawEdgeChoice_ext_targetLast {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (c d : MarkedRawEdgeChoice hZ s) (ht : c.target=d.target) (hs : c.store=d.store)
    (hp : c.promotions=d.promotions)
    (hl : markedRawEdgeTargetLast s.2.2 c.promotions c.fresh=
      markedRawEdgeTargetLast s.2.2 d.promotions d.fresh) : c=d := by
  rcases c with ⟨tc,sc,pc,fc,hpc,hbc⟩
  rcases d with ⟨td,sd,pd,fd,hpd,hbd⟩
  dsimp only at ht hs hp hl
  subst td; subst sd; subst pd
  have hf : fc=fd := by
    funext j
    have hh := congrFun hl j
    unfold markedRawEdgeTargetLast at hh
    split at hh
    · exact (cast_inj _).mp hh
    · rename_i i hi
      apply @Subsingleton.elim _ ?_ (fc j) (fd j)
      split
      · rename_i hn
        rw [hi] at hn
        cases hn
      · infer_instance
  subst fd
  rfl

def markedRawEdgeChoiceReindexEquiv {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s s' : MarkedRawState P (pads+1) B Z)
    (e : (j : J) → Fin (s'.2.2.1.1 j : ℕ) ≃ Fin (s.2.2.1.1 j : ℕ))
    (he : ∀ j i, s'.2.2.2 j i=s.2.2.2 j (e j i)) :
    MarkedRawEdgeChoice hZ s ≃ MarkedRawEdgeChoice hZ s' where
  toFun := markedRawEdgeChoiceReindex hZ s s' e he
  invFun := markedRawEdgeChoiceReindex hZ s' s (fun j => (e j).symm)
    (fun j i => by simpa only [Equiv.apply_symm_apply] using (he j ((e j).symm i)).symm)
  left_inv c := by
    refine markedRawEdgeChoice_ext_targetLast hZ s _ c ?_ ?_ ?_ ?_
    · rfl
    · rfl
    · funext j
      simp only [Equiv.symm_symm, Option.map_map]
      simp
    · rw [markedRawEdgeChoiceReindex_targetLast, markedRawEdgeChoiceReindex_targetLast]
  right_inv c := by
    refine markedRawEdgeChoice_ext_targetLast hZ s' _ c ?_ ?_ ?_ ?_
    · rfl
    · rfl
    · funext j
      simp only [Equiv.symm_symm, Option.map_map]
      simp
    · rw [markedRawEdgeChoiceReindex_targetLast, markedRawEdgeChoiceReindex_targetLast]

end ArtinMatthews
