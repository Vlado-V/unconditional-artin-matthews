module

public import ArtinMatthews.MarkedMinorArcRawEdgeFullTranspose


set_option backward.privateInPublic true
@[expose] public section

/-! Literal store/promote actions with a joint coefficient depending on
both Boolean flag families.  Source and target cutoffs remain in the
actual choice type; transposition will exchange these two families. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators

abbrev MarkedRawEdgePatternKernel {J : Type*} [Fintype J]
    (P : J → Finset Nat.Primes) (pads B : ℕ) (Z : Finset (ℤ × ℤ)) :=
  (J → Bool) → (J → Bool) → MarkedRawState P (pads+1) B Z →
    MarkedRawState P (pads+1) B Z → ℂ

def markedRawEdgeChoicePromoted {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    {hZ : ∀ z ∈ Z, IsCoprime z.1 z.2} {s : MarkedRawState P (pads+1) B Z}
    (c : MarkedRawEdgeChoice hZ s) : J → Bool := fun j => (c.promotions j).isSome

def markedRawEdgePatternReverse {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (A : MarkedRawEdgePatternKernel P pads B Z) : MarkedRawEdgePatternKernel P pads B Z :=
  fun p q s t => A q p t s

@[simp] theorem markedRawEdgePatternReverse_reverse {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (A : MarkedRawEdgePatternKernel P pads B Z) :
    markedRawEdgePatternReverse (markedRawEdgePatternReverse A) = A := rfl

def markedRawEdgePatternApply {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (δ γ : J → ℂ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (A : MarkedRawEdgePatternKernel P pads B Z)
    (f : MarkedRawState P (pads+1) B Z → ℂ) (s : MarkedRawState P (pads+1) B Z) : ℂ :=
  ∑ c : MarkedRawEdgeChoice hZ s,
    markedRawEdgeChoiceCharge δ γ hZ s c * markedRawEdgeChoiceFreshMass ν hZ s c *
      A (markedRawEdgeChoicePromoted c) c.store s (markedRawEdgeTargetState hZ s c) *
      f (markedRawEdgeTargetState hZ s c)

theorem markedRawEdgePatternApply_const {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (δ γ : J → ℂ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (K : MarkedRawState P (pads+1) B Z → MarkedRawState P (pads+1) B Z → ℂ)
    (f : MarkedRawState P (pads+1) B Z → ℂ) :
    markedRawEdgePatternApply ν δ γ hZ (fun _ _ => K) f =
      markedRawEdgeChargedApply ν δ γ hZ K f := rfl

theorem markedRawEdge_degree_promoted_flags {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (x : Z) (active : MarkedRawActive P (pads+1))
    (y : Z) (a : MarkedRawEdgeDegreeShape J B)
    (data : MarkedRawEdgeDegreePayload P y.1 (hZ _ y.2) a) :
    markedRawEdgeChoicePromoted (markedRawEdgeDegreeMemoryChoice hZ x active y a data).2 =
      a.1.promoted := by
  funext j
  exact markedRawEdge_degree_promoted hZ x active y a data j

end
end ArtinMatthews
