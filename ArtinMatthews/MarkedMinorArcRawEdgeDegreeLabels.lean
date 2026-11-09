module

public import ArtinMatthews.MarkedMinorArcRawEdgeSymmetryChoices


set_option backward.privateInPublic true
@[expose] public section

/-! Exact replacement of dependent fresh-label choices by their actual target
labels. A promoted group contributes a singleton constrained label, never an
extra prime choice, even when several old particles have the same prime. -/
namespace ArtinMatthews
noncomputable section
set_option backward.isDefEq.respectTransparency false
-- Expose the imported dependent Option matcher at its pinned declaration.
set_option linter.auxLemma false
set_option allowUnsafeReducibility true in
attribute [local reducible] MarkedRawEdgeFreshLabels.match_1 markedRawEdgeTargetLast.match_1

/-- One group's dependent fresh choice is equivalent to its constrained target label. -/
def markedRawEdgeDegreeFreshEquiv {X : Type*} {k : ℕ} (a : Fin k → X)
    (p : Option (Fin k)) :
    (Option.casesOn p X (fun _ => PUnit)) ≃
      {x : X // ∀ i, p = some i → x = a i} := by
  cases p with
  | none =>
    exact { toFun := fun x => ⟨x, by simp⟩
            invFun := Subtype.val
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
  | some i =>
    exact { toFun := fun _ => ⟨a i, by intro j h; cases Option.some.inj h; rfl⟩
            invFun := fun _ => PUnit.unit
            left_inv := fun _ => Subsingleton.elim _ _
            right_inv := fun x => Subtype.ext (x.2 i rfl).symm }

def markedRawEdgeDegreeFreshTarget {X : Type*} {k : ℕ} (a : Fin k → X)
    (p : Option (Fin k)) (u : Option.casesOn p X (fun _ => PUnit)) : X :=
  match h : p with
  | none => by simpa only [h] using u
  | some i => a i

theorem markedRawEdgeDegreeFreshEquiv_value {X : Type*} {k : ℕ}
    (a : Fin k → X) (p : Option (Fin k)) (u : Option.casesOn p X (fun _ => PUnit)) :
    (markedRawEdgeDegreeFreshEquiv a p u).1=markedRawEdgeDegreeFreshTarget a p u := by
  cases p <;> rfl

theorem markedRawEdgeDegreeFreshEquiv_none {X : Type*} {k : ℕ}
    (a : Fin k → X) (p : Option (Fin k)) (u : Option.casesOn p X (fun _ => PUnit))
    (hp : p=none) : HEq (markedRawEdgeDegreeFreshEquiv a p u).1 u := by
  subst p
  rfl

theorem markedRawEdgeDegreeFreshEquiv_some {X : Type*} {k : ℕ}
    (a : Fin k → X) (p : Option (Fin k)) (u : Option.casesOn p X (fun _ => PUnit))
    (i : Fin k) (hp : p=some i) : (markedRawEdgeDegreeFreshEquiv a p u).1=a i := by
  subst p
  rfl

/-- All groups retain exactly one coordinate for each actual target label;
promoted coordinates are constrained by their selected old indices. -/
def markedRawEdgeDegreeLabelsEquiv {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {B : ℕ} (m : MarkedRawMemory P B)
    (prom : MarkedRawEdgePromotions m) :
    MarkedRawEdgeFreshLabels prom ≃
      {a : (j : J) → ↥(P j) // ∀ j k, prom j = some k → a j = (m.2 j k).1} := by
  unfold MarkedRawEdgeFreshLabels MarkedRawEdgeFreshLabels.match_1
  exact (Equiv.piCongrRight (fun j => markedRawEdgeDegreeFreshEquiv
    (fun k => (m.2 j k).1) (prom j))).trans Equiv.subtypePiEquivPi.symm

/-- The equivalent labels are the actual labels used by the literal edge. -/
theorem markedRawEdgeDegreeLabelsEquiv_value {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {B : ℕ} (m : MarkedRawMemory P B)
    (prom : MarkedRawEdgePromotions m) (fresh : MarkedRawEdgeFreshLabels prom) :
    (markedRawEdgeDegreeLabelsEquiv m prom fresh).1 = markedRawEdgeTargetLast m prom fresh := by
  funext j
  symm
  unfold markedRawEdgeTargetLast
  split
  · rename_i hn
    unfold MarkedRawEdgeFreshLabels MarkedRawEdgeFreshLabels.match_1 at *
    have htype : (Option.casesOn (prom j) ↥(P j) (fun _ => PUnit))=↥(P j) := by
      rw [hn]
    change _ = (markedRawEdgeDegreeFreshEquiv (fun k => (m.2 j k).1) (prom j) (fresh j)).1
    change cast htype (fresh j) = _
    exact eq_of_heq ((cast_heq htype (fresh j)).trans (markedRawEdgeDegreeFreshEquiv_none
      (fun k => (m.2 j k).1) (prom j) (fresh j) hn).symm)
  · rename_i k hk
    unfold MarkedRawEdgeFreshLabels MarkedRawEdgeFreshLabels.match_1 at *
    change _ = (markedRawEdgeDegreeFreshEquiv (fun k => (m.2 j k).1) (prom j) (fresh j)).1
    exact (markedRawEdgeDegreeFreshEquiv_some (fun k => (m.2 j k).1) (prom j) (fresh j) k hk).symm

end
end ArtinMatthews
