module

public import ArtinMatthews.MarkedMinorArcDirtyRawEdgeChoices


set_option backward.privateInPublic true
@[expose] public section

/-! Literal fresh coordinates of a fixed actual promotion pattern. Promoted
slots have singleton fresh-label types, hence introduce no size factor. -/
noncomputable section
namespace ArtinMatthews

open scoped BigOperators

def markedDirtyEdgeFreshTuple {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {B : ℕ} (m : MarkedRawMemory P B)
    (prom : MarkedRawEdgePromotions m) (fresh : MarkedRawEdgeFreshLabels prom) :
    (j : markedDirtyEdgeFreshGroups prom) → ↥(P j.1) :=
  fun j => markedRawEdgeTargetLast m prom fresh j.1

theorem markedDirtyEdgeFreshTuple_injective {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {B : ℕ} (m : MarkedRawMemory P B)
    (prom : MarkedRawEdgePromotions m) : Function.Injective (markedDirtyEdgeFreshTuple m prom) := by
  classical
  intro a b hab
  funext j
  by_cases hp : prom j=none
  · have hj : j ∈ markedDirtyEdgeFreshGroups prom := by simp [markedDirtyEdgeFreshGroups,hp]
    have hh := congrFun hab ⟨j,hj⟩
    change markedRawEdgeTargetLast m prom a j=markedRawEdgeTargetLast m prom b j at hh
    rw [markedDirtyEdgeTargetLast_none m prom a j hp,markedDirtyEdgeTargetLast_none m prom b j hp] at hh
    let β : Option (Fin (m.1.1 j:ℕ)) → Type := fun o => match o with | none => ↥(P j) | some _ => PUnit
    exact (Equiv.cast (congrArg β hp)).injective hh
  · have hs : Subsingleton (match prom j with | none => ↥(P j) | some _ => PUnit) := by
      split
      · rename_i hn
        exact False.elim (hp hn)
      · infer_instance
    exact hs.elim _ _

theorem markedDirtyEdgeFreshProduct_tuple {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {B : ℕ} (m : MarkedRawMemory P B)
    (prom : MarkedRawEdgePromotions m) (fresh : MarkedRawEdgeFreshLabels prom) :
    markedDirtyEdgeFreshProduct m prom fresh =
      ∏ j : markedDirtyEdgeFreshGroups prom, ((markedDirtyEdgeFreshTuple m prom fresh j).1:ℕ) :=
  (Finset.prod_coe_sort _ (fun j => ((markedRawEdgeTargetLast m prom fresh j).1:ℕ))).symm

theorem markedDirtyEdgeChoicePrimeMass_fresh_tuple {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (s : MarkedRawState P (pads+1) B Z) (choice : MarkedRawEdgeChoice hZ s) :
    markedRawEdgeChoicePrimeMass ν V hZ s choice=
      finiteProductMass (fun j : markedDirtyEdgeFreshGroups choice.promotions => ν j.1)
        (markedDirtyEdgeFreshTuple s.2.2 choice.promotions choice.fresh)*
      (∏ j ∈ markedDirtyEdgePromotedGroups choice.promotions, (V j)⁻¹) := by
  rw [markedDirtyEdgeChoicePrimeMass_split]
  congr 1
  exact (Finset.prod_coe_sort _ (fun j => ν j (markedRawEdgeTargetLast s.2.2 choice.promotions choice.fresh j))).symm

end ArtinMatthews
