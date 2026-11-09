module

public import ArtinMatthews.MarkedMemoryIndependentScalarProduct


set_option backward.privateInPublic true
@[expose] public section

/-! On the source schedule, the direct independent scalar is the product
of -eta times the carried-particle hit for births/deaths, and 1-eta times
that hit for retained pending particles. The actual-history source
comparison uses the established anchor-admissibility gate. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
  {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  {A : J → Type*} [∀ j, DecidableEq (A j)] [∀ j, Fintype (A j)]
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)
  (order : Fin n → J → Equiv.Perm (Fin pads))

local notation "history" => markedMemoryIndependentHistory hZ d order
local notation "addr" => markedMemoryIndependentAddressEquiv hZ d order

def markedMemoryIndependentLineHit (a : Σ j, A j) (v : Fin (n+1)) : ℝ :=
  if MarkedRawParticleHits (P a.1) (d.position v.val).1 (hZ _ (d.position v.val).2)
    (d.particle a.1 a.2) then 1 else 0

def markedMemoryIndependentLifespanSourceScalar (q : ℝ) (a : Σ j, A j) : ℝ :=
  ∏ v : Fin (n+1),
    (if a.2 ∈ markedMemoryIndependentQueue hZ d (2*v.val) a.1 then
      (if (d.lifespan a.1).last a.2 = 2*v.val then
        -markedMemoryEta q n v * markedMemoryIndependentLineHit hZ d a v
      else 1-markedMemoryEta q n v * markedMemoryIndependentLineHit hZ d a v)
     else 1) *
    (if a.2 ∈ (d.lifespan a.1).births (2*v.val) then
      -markedMemoryEta q n v * markedMemoryIndependentLineHit hZ d a v else 1)

omit [DecidableEq J] in
theorem markedMemoryIndependentLineHit_death (a : Σ j, A j) (v : Fin (n+1))
    (hm : a.2 ∈ markedMemoryIndependentQueue hZ d (2*v.val) a.1)
    (hd : (d.lifespan a.1).last a.2 = 2*v.val) :
    markedMemoryIndependentLineHit hZ d a v = 1 := by
  have hs := (markedMemoryPendingQueueAt_mem (d.lifespan a.1) (2*v.val) (by omega) a.2).mp hm
  have hh := d.ghost_death_hit v.val (by omega) a.1 a.2 hs.1 hd hs.2.2
  exact ite_eq_left hh

omit [DecidableEq J] [∀ j, DecidableEq (A j)] in
theorem markedMemoryIndependentLineHit_birth (a : Σ j, A j) (v : Fin (n+1))
    (hb : a.2 ∈ (d.lifespan a.1).births (2*v.val)) :
    markedMemoryIndependentLineHit hZ d a v = 1 := by
  have ha := d.ghost_birth_anchor v.val (by omega) a.1 a.2 hb
  have hh : MarkedRawParticleHits (P a.1) (d.position v.val).1 (hZ _ (d.position v.val).2)
      (d.particle a.1 a.2) := by
    rw [ha]
    rfl
  exact ite_eq_left hh

omit [DecidableEq J] in
theorem markedMemoryIndependentLifespanScalar_source (q : ℝ) (a : Σ j, A j) :
    markedMemoryIndependentLifespanScalar hZ d (markedMemoryHistoryVisitSchedule q n) 0 a =
      markedMemoryIndependentLifespanSourceScalar hZ d q a := by
  unfold markedMemoryIndependentLifespanScalar markedMemoryIndependentLifespanSourceScalar
  apply Finset.prod_congr rfl
  intro v _
  apply congrArg₂ (fun x y : ℝ => x*y)
  · by_cases hm : a.2 ∈ markedMemoryIndependentQueue hZ d (2*v.val) a.1
    · simp only [hm, ite_true]
      by_cases hd : (d.lifespan a.1).last a.2 = 2*v.val
      · rw [markedMemoryIndependentLineHit_death hZ d a v hm hd]
        simp only [markedMemoryIndependentOldScalar, hd, ite_true, Nat.zero_add,
          markedMemoryHistoryVisitSchedule_vertex, markedMemoryEta, mul_one]
      · unfold markedMemoryIndependentOldScalar markedMemoryIndependentLineHit
        simp only [hd, ite_false, Nat.zero_add, markedMemoryHistoryVisitSchedule_vertex, markedMemoryEta]
        split_ifs <;> ring
    · simp only [hm, ite_false]
  · by_cases hb : a.2 ∈ (d.lifespan a.1).births (2*v.val)
    · rw [markedMemoryIndependentLineHit_birth hZ d a v hb]
      simp only [hb, ite_true, Nat.zero_add, markedMemoryHistoryVisitSchedule_vertex, markedMemoryEta, mul_one]
    · simp only [hb, ite_false]

omit [DecidableEq J] in
theorem markedMemoryIndependentLifespanSourceScalar_endpoints (q : ℝ) (a : Σ j, A j) :
    markedMemoryIndependentLifespanSourceScalar hZ d q a =
      ∏ v : Fin (n+1),
        (if (d.lifespan a.1).first a.2 ≤ 2*v.val ∧ 2*v.val ≤ (d.lifespan a.1).last a.2 ∧
            ¬ (d.lifespan a.1).active (2*v.val) a.2 then
          (if (d.lifespan a.1).last a.2 = 2*v.val then
            -markedMemoryEta q n v * markedMemoryIndependentLineHit hZ d a v
          else 1-markedMemoryEta q n v * markedMemoryIndependentLineHit hZ d a v)
         else 1) *
        (if (d.lifespan a.1).first a.2 = 2*v.val+1 ∧ 2*v.val+1 ≤ (d.lifespan a.1).last a.2 ∧
            ¬ (d.lifespan a.1).active (2*v.val) a.2 then
          -markedMemoryEta q n v * markedMemoryIndependentLineHit hZ d a v else 1) := by
  unfold markedMemoryIndependentLifespanSourceScalar
  apply Finset.prod_congr rfl
  intro v _
  simp only [markedMemoryIndependentQueue,
    markedMemoryPendingQueueAt_mem (d.lifespan a.1) (2*v.val) (by omega),
    (d.lifespan a.1).ghost_births (2*v.val) (by omega) (by omega)]

theorem markedMemoryIndependent_sourceScalar
    (ha : MarkedMemoryHistoryAnchorAdmissible hZ history) (q : ℝ) (a : Σ j, A j) :
    markedMemoryHistoryLifespanSourceScalar hZ history q ((addr).symm a) =
      markedMemoryIndependentLifespanSourceScalar hZ d q a := by
  rw [← markedMemoryHistoryLifespanScalar_source hZ history ha,
    markedMemoryIndependent_lifespanScalar, markedMemoryIndependentLifespanScalar_source]

theorem markedMemoryIndependent_sourceScalar_of_weight_ne_zero
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ)
    (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ) (q : ℝ)
    (hw : markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ
      (markedMemoryHistoryVisitSchedule q n) χ n 0 history ≠ 0) (a : Σ j, A j) :
    markedMemoryHistoryLifespanSourceScalar hZ history q ((addr).symm a) =
      markedMemoryIndependentLifespanSourceScalar hZ d q a :=
  markedMemoryIndependent_sourceScalar hZ d order
    (markedMemoryHistoryAnchorAdmissible_of_weight_ne_zero ν V hZ ψ η d₀ Y Q ρ
      (markedMemoryHistoryVisitSchedule q n) χ n 0 history hw) q a

end
end ArtinMatthews
