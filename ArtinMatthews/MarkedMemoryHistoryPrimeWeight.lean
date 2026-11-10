module

public import ArtinMatthews.MarkedMemoryHistoryBirthLabels
public import ArtinMatthews.MarkedMemoryHistoryLifespans
public import ArtinMatthews.MarkedMemoryHistoryWeightTelescope
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Prime-mass assembly for the literal chronological signed weight.
Every actual ghost and fresh-edge birth contributes its own nu atom;
ghost births also contribute V, and only real old-memory promotions pay
V inverse. Signs, birth factorials and both slot probabilities remain in
the explicitly displayed residual coefficient. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

universe u

variable {J : Type u} [Fintype J] [DecidableEq J]
  {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
  (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)

/-- An actual old-memory retrieval in the original edge choice. -/
abbrev MarkedMemoryEdgePromotionIndex {s : MarkedRawState P (pads+1) B Z}
    (edge : MarkedMemoryEdgeChoice hZ s) := {j : J // edge.2.1.promotions j ≠ none}

def MarkedMemoryHistoryPromotionIndex :
    {n : ℕ} → {s : MarkedRawState P (pads+1) B Z} →
      MarkedMemoryChronologicalHistory hZ n s → Type u
  | 0,_,_ => PEmpty.{u+1}
  | _+1,_,history => MarkedMemoryEdgePromotionIndex hZ history.2.1 ⊕
      MarkedMemoryHistoryPromotionIndex history.2.2

@[instance_reducible]
def markedMemoryHistoryPromotionIndex_fintype :
    {n : ℕ} → {s : MarkedRawState P (pads+1) B Z} →
      (history : MarkedMemoryChronologicalHistory hZ n s) →
        Fintype (MarkedMemoryHistoryPromotionIndex hZ history)
  | 0,_,_ => inferInstanceAs (Fintype PEmpty.{u+1})
  | _+1,_,history => by
      letI := markedMemoryHistoryPromotionIndex_fintype history.2.2
      change Fintype (MarkedMemoryEdgePromotionIndex hZ history.2.1 ⊕
        MarkedMemoryHistoryPromotionIndex hZ history.2.2)
      infer_instance

attribute [instance] markedMemoryHistoryPromotionIndex_fintype

def markedMemoryHistoryPromotionGroup :
    {n : ℕ} → {s : MarkedRawState P (pads+1) B Z} →
      (history : MarkedMemoryChronologicalHistory hZ n s) →
        MarkedMemoryHistoryPromotionIndex hZ history → J
  | 0,_,_ => PEmpty.elim
  | _+1,_,history => Sum.elim Subtype.val (markedMemoryHistoryPromotionGroup history.2.2)

/-- The mass of exactly the actual performed births, including the V
creation factor only for a ghost birth. -/
def markedMemoryHistoryBirthMass {n : ℕ} {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) : ℝ :=
  ∏ b : MarkedMemoryHistoryBirths hZ history,
    let p := markedMemoryHistoryBirthLabel hZ history b
    (if markedMemoryHistoryBirthIsGhost hZ history b then V p.1 else 1) * ν p.1 p.2

def markedMemoryHistoryPromotionMass {n : ℕ} {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) : ℝ :=
  ∏ r : MarkedMemoryHistoryPromotionIndex hZ history,
    (V (markedMemoryHistoryPromotionGroup hZ history r))⁻¹

def markedMemoryHistoryPrimeMass {n : ℕ} {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) : ℝ :=
  markedMemoryHistoryBirthMass ν V hZ history * markedMemoryHistoryPromotionMass V hZ history

/-- The original ghost signs, surviving-hit powers and literal birth
factorials after separating the V nu birth atoms. -/
def markedMemoryGhostResidual (qStage : ℝ) (s : MarkedRawState P (pads+1) B Z)
    (ghost : MarkedMemoryGhostChoice hZ s) : ℝ :=
  ∏ j, ((-(1-qStage))^(ghost.deletion j).card *
    qStage^((markedRawGroupHitIndices s.2.2 j s.1.1 (hZ _ s.1.2) \ ghost.deletion j).card) *
    (-(1-qStage))^(ghost.sizes.1 j : ℕ)) / ((ghost.sizes.1 j : ℕ).factorial : ℝ)

def markedMemoryEdgeResidual (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q : ℝ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (s : MarkedRawState P (pads+1) B Z) (edge : MarkedMemoryEdgeChoice hZ s) : ℂ :=
  ((Fintype.card (MarkedMemorySlotPermutations J (pads+1)) : ℂ)⁻¹) *
    markedRawEdgeChoiceCoefficient hZ ψ η d₀ Y Q 1 χ (markedRawSlotEquiv edge.1 s) edge.2.1 *
      ((Fintype.card (MarkedMemorySlotPermutations J (pads+1)) : ℂ)⁻¹)

def markedMemoryHistoryResidual (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q : ℝ)
    (qStage : ℕ → ℝ) (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ) :
    (n j : ℕ) → {s : MarkedRawState P (pads+1) B Z} →
      MarkedMemoryChronologicalHistory hZ n s → ℂ
  | 0,j,s,ghost => (markedMemoryGhostResidual hZ (qStage j) s ghost : ℂ)
  | n+1,j,s,history => (markedMemoryGhostResidual hZ (qStage j) s history.1 : ℂ) *
      markedMemoryEdgeResidual hZ ψ η d₀ Y Q (χ j)
        (markedMemoryGhostChoiceTarget hZ s history.1) history.2.1 *
      markedMemoryHistoryResidual ψ η d₀ Y Q qStage χ n (j+1) history.2.2

omit [DecidableEq J] in
theorem markedMemoryGhostChoiceWeight_prime_factor (qStage : ℝ)
    (s : MarkedRawState P (pads+1) B Z) (ghost : MarkedMemoryGhostChoice hZ s) :
    markedMemoryGhostChoiceWeight ν V qStage 1 hZ s ghost =
      ((∏ b : MarkedMemoryGhostBirthIndex ghost, V b.1 * ν b.1 (ghost.births b.1 b.2) : ℝ) : ℂ) *
        (markedMemoryGhostResidual hZ qStage s ghost : ℂ) := by
  rw [markedMemoryGhostChoiceWeight_one]
  unfold markedMemoryGhostReducedCoefficient markedRawGhostBirthMass markedMemoryGhostResidual
  rw [Fintype.prod_sigma]
  push_cast
  norm_cast
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_pow]
  ring

omit [DecidableEq J] in
theorem markedMemoryEdgeChoicePrimeMass_split
    (s : MarkedRawState P (pads+1) B Z) (edge : MarkedMemoryEdgeChoice hZ s) :
    markedRawEdgeChoicePrimeMass ν V hZ (markedRawSlotEquiv edge.1 s) edge.2.1 =
      (∏ b : MarkedMemoryEdgeBirthIndex edge,
        let p := markedMemoryEdgeBirthLabel edge b
        ν p.1 p.2) *
      ∏ r : MarkedMemoryEdgePromotionIndex hZ edge, (V r.1)⁻¹ := by
  let w (j : J) := if edge.2.1.promotions j = none then
    ν j (markedRawEdgeTargetLast (markedRawSlotEquiv edge.1 s).2.2 edge.2.1.promotions edge.2.1.fresh j)
    else (V j)⁻¹
  have hw : markedRawEdgeChoicePrimeMass ν V hZ (markedRawSlotEquiv edge.1 s) edge.2.1 = ∏ j, w j := by
    unfold markedRawEdgeChoicePrimeMass
    apply Finset.prod_congr rfl
    intro j _
    split <;> rename_i hp
    · dsimp only [w]
      simp only [hp, ite_true]
      congr 1
      unfold markedRawEdgeTargetLast
      split
      · rfl
      · rename_i k hk
        rw [hp] at hk
        cases hk
    · simp only [w, hp, reduceCtorEq, ite_false]
  rw [hw, ← Fintype.prod_subtype_mul_prod_subtype (fun j => edge.2.1.promotions j = none) w]
  congr 1
  · apply Finset.prod_congr rfl
    intro b _
    simp only [w, b.2, ite_true, markedMemoryEdgeBirthLabel]
  · apply Finset.prod_congr rfl
    intro r _
    simp only [w, r.2, ite_false]

theorem markedMemoryEdgeChoiceWeight_prime_factor
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q : ℝ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (s : MarkedRawState P (pads+1) B Z) (edge : MarkedMemoryEdgeChoice hZ s) :
    markedMemoryEdgeChoiceWeight ν V hZ ψ η d₀ Y Q 1 χ s edge =
      (((∏ b : MarkedMemoryEdgeBirthIndex edge,
        let p := markedMemoryEdgeBirthLabel edge b
        ν p.1 p.2) *
      ∏ r : MarkedMemoryEdgePromotionIndex hZ edge, (V r.1)⁻¹ : ℝ) : ℂ) *
        markedMemoryEdgeResidual hZ ψ η d₀ Y Q χ s edge := by
  unfold markedMemoryEdgeChoiceWeight markedMemoryEdgeResidual
  rw [markedMemoryEdgeChoicePrimeMass_split]
  ring

omit [DecidableEq J] in
theorem markedMemoryHistoryBirthMass_zero (s : MarkedRawState P (pads+1) B Z)
    (ghost : MarkedMemoryGhostChoice hZ s) :
    markedMemoryHistoryBirthMass ν V hZ (n := 0) ghost =
      ∏ b : MarkedMemoryGhostBirthIndex ghost, V b.1 * ν b.1 (ghost.births b.1 b.2) := rfl

omit [DecidableEq J] in
theorem markedMemoryHistoryBirthMass_succ {n : ℕ} {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ (n+1) s) :
    markedMemoryHistoryBirthMass ν V hZ history =
      (∏ b : MarkedMemoryGhostBirthIndex history.1, V b.1 * ν b.1 (history.1.births b.1 b.2)) *
      ((∏ b : MarkedMemoryEdgeBirthIndex history.2.1,
        let p := markedMemoryEdgeBirthLabel history.2.1 b
        ν p.1 p.2) * markedMemoryHistoryBirthMass ν V hZ history.2.2) := by
  rcases history with ⟨ghost,edge,tail⟩
  unfold markedMemoryHistoryBirthMass
  change (∏ b : MarkedMemoryGhostBirthIndex ghost ⊕
      (MarkedMemoryEdgeBirthIndex edge ⊕ MarkedMemoryHistoryBirths hZ tail), _) = _
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
  apply congrArg₂ (fun x y : ℝ => x * y)
  · apply Finset.prod_congr rfl
    intro b _
    rfl
  · apply congrArg₂ (fun x y : ℝ => x * y)
    · apply Finset.prod_congr rfl
      intro b _
      change (1 : ℝ) * _ = _
      exact one_mul _
    · apply Finset.prod_congr rfl
      intro b _
      rfl


omit [DecidableEq J] in
theorem markedMemoryHistoryPromotionMass_zero (s : MarkedRawState P (pads+1) B Z)
    (ghost : MarkedMemoryGhostChoice hZ s) :
    markedMemoryHistoryPromotionMass V hZ (n := 0) ghost = 1 := by
  change (∏ _ : PEmpty.{u+1}, _) = 1
  exact Fintype.prod_empty _

omit [DecidableEq J] in
theorem markedMemoryHistoryPromotionMass_succ {n : ℕ} {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ (n+1) s) :
    markedMemoryHistoryPromotionMass V hZ history =
      (∏ r : MarkedMemoryEdgePromotionIndex hZ history.2.1, (V r.1)⁻¹) *
        markedMemoryHistoryPromotionMass V hZ history.2.2 := by
  rcases history with ⟨ghost,edge,tail⟩
  unfold markedMemoryHistoryPromotionMass
  change (∏ r : MarkedMemoryEdgePromotionIndex hZ edge ⊕
      MarkedMemoryHistoryPromotionIndex hZ tail, _) = _
  rw [Fintype.prod_sum_type]
  rfl

/-- The complete signed chronological coefficient, derived from its
actual dependent choices. No history/lifespan factorization is a premise. -/
theorem markedMemoryChronologicalWeight_prime_factor
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q : ℝ)
    (qStage : ℕ → ℝ) (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ)
    (n j : ℕ) {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) :
    markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q 1 qStage χ n j history =
      (markedMemoryHistoryPrimeMass ν V hZ history : ℂ) *
        markedMemoryHistoryResidual hZ ψ η d₀ Y Q qStage χ n j history := by
  induction n generalizing j s with
  | zero =>
    change MarkedMemoryGhostChoice hZ s at history
    change markedMemoryGhostChoiceWeight ν V (qStage j) 1 hZ s history = _
    rw [markedMemoryGhostChoiceWeight_prime_factor]
    simp only [markedMemoryHistoryPrimeMass,
      markedMemoryHistoryBirthMass_zero, markedMemoryHistoryPromotionMass_zero, mul_one]
    rfl
  | succ n ih =>
    rcases history with ⟨ghost,edge,tail⟩
    change markedMemoryGhostChoiceWeight ν V (qStage j) 1 hZ s ghost *
      markedMemoryEdgeChoiceWeight ν V hZ ψ η d₀ Y Q 1 (χ j)
        (markedMemoryGhostChoiceTarget hZ s ghost) edge *
      markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q 1 qStage χ n (j+1) tail = _
    rw [markedMemoryGhostChoiceWeight_prime_factor, markedMemoryEdgeChoiceWeight_prime_factor, ih]
    have hb := markedMemoryHistoryBirthMass_succ ν V hZ (n := n)
      (show MarkedMemoryChronologicalHistory hZ (n+1) s from ⟨ghost,edge,tail⟩)
    have hp := markedMemoryHistoryPromotionMass_succ V hZ (n := n)
      (show MarkedMemoryChronologicalHistory hZ (n+1) s from ⟨ghost,edge,tail⟩)
    simp only [markedMemoryHistoryPrimeMass]
    rw [hb, hp]
    change _ = _ * ((markedMemoryGhostResidual hZ (qStage j) s ghost : ℂ) *
      markedMemoryEdgeResidual hZ ψ η d₀ Y Q (χ j)
        (markedMemoryGhostChoiceTarget hZ s ghost) edge *
      markedMemoryHistoryResidual hZ ψ η d₀ Y Q qStage χ n (j+1) tail)
    push_cast
    ring

end
end ArtinMatthews
