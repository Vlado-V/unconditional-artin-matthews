module

public import ArtinMatthews.MarkedMinorArcRawEdgeSymmetryCoefficients


set_option backward.privateInPublic true
@[expose] public section

/-! The original store/promote row operator preserves the actual
symmetric-pending domain, including the concrete physical cutoffs. -/
noncomputable section
namespace ArtinMatthews
open scoped BigOperators

theorem markedRawEdgeApply_permute {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (χ f : MarkedRawState P (pads+1) B Z → ℂ)
    (hχ : ∀ z a, MarkedRawMemorySymmetric (fun m => χ (z,(a,m))))
    (hf : ∀ z a, MarkedRawMemorySymmetric (fun m => f (z,(a,m))))
    (z : Z) (a : MarkedRawActive P (pads+1)) (m : MarkedRawMemory P B)
    (σ : (j : J) → Equiv.Perm (Fin (m.1.1 j : ℕ))) :
    markedRawEdgeApply ν V hZ ψ η d₀ Y Q ρ χ f (z,(a,markedRawMemoryPermute m σ)) =
      markedRawEdgeApply ν V hZ ψ η d₀ Y Q ρ χ f (z,(a,m)) := by
  classical
  unfold markedRawEdgeApply
  rw [← Equiv.sum_comp (markedRawEdgeChoicePermute hZ z a m σ)]
  apply Finset.sum_congr rfl
  intro c _
  rw [markedRawEdgeChoicePrimeMass_permute,
    markedRawEdgeChoiceCoefficient_permute hZ ψ η d₀ Y Q ρ χ hχ,
    markedRawEdgeTargetState_symmetric_permute hZ z a m σ f hf]

theorem markedRawEdgeApply_symmetric {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (χ f : MarkedRawState P (pads+1) B Z → ℂ)
    (hχ : ∀ z a, MarkedRawMemorySymmetric (fun m => χ (z,(a,m))))
    (hf : ∀ z a, MarkedRawMemorySymmetric (fun m => f (z,(a,m))))
    (z : Z) (a : MarkedRawActive P (pads+1)) :
    MarkedRawMemorySymmetric (fun m => markedRawEdgeApply ν V hZ ψ η d₀ Y Q ρ χ f (z,(a,m))) :=
  fun m σ => markedRawEdgeApply_permute ν V hZ ψ η d₀ Y Q ρ χ f hχ hf z a m σ

/-- Physical multipliers use position and active labels, so their
required symmetry is proved rather than supplied as an operator premise. -/
theorem markedRawEdgeApply_memoryIndependent_symmetric {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (χ : Z → MarkedRawActive P (pads+1) → ℂ)
    (f : MarkedRawState P (pads+1) B Z → ℂ)
    (hf : ∀ z a, MarkedRawMemorySymmetric (fun m => f (z,(a,m))))
    (z : Z) (a : MarkedRawActive P (pads+1)) :
    MarkedRawMemorySymmetric (fun m => markedRawEdgeApply ν V hZ ψ η d₀ Y Q ρ
      (fun s => χ s.1 s.2.1) f (z,(a,m))) :=
  markedRawEdgeApply_symmetric ν V hZ ψ η d₀ Y Q ρ _ f
    (markedRawMemoryIndependent_symmetric χ) hf z a

theorem markedRawEdgeApply_boundary_symmetric {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (χ : Z → MarkedRawActive P (pads+1) → ℂ)
    (z₀ z : Z) (a : MarkedRawActive P (pads+1)) :
    MarkedRawMemorySymmetric (fun m : MarkedRawMemory P B =>
      markedRawEdgeApply ν V hZ ψ η d₀ Y Q ρ
        (fun s => χ s.1 s.2.1) (markedRawBoundary z₀) (z,(a,m))) :=
  markedRawEdgeApply_memoryIndependent_symmetric ν V hZ ψ η d₀ Y Q ρ χ
    (markedRawBoundary z₀) (markedRawBoundary_symmetric z₀) z a

/-- The actual first-good physical cutoff retains the same invariant
domain, including its copied-product dyad and geometric good-state test. -/
theorem markedRawEdgeApply_firstGood_memoryIndependent_symmetric {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (r d₀ Y Q ρ : ℝ) (w : Z → ℤ × ℤ) (χ : Z → MarkedRawActive P (pads+1) → ℂ)
    (f : MarkedRawState P (pads+1) B Z → ℂ)
    (hf : ∀ z a, MarkedRawMemorySymmetric (fun m => f (z,(a,m))))
    (z : Z) (a : MarkedRawActive P (pads+1)) :
    MarkedRawMemorySymmetric (fun m => markedRawEdgeApply ν V hZ ψ η d₀ Y Q ρ
      (markedRawFirstGoodCutoff r d₀ Y w (fun s => χ s.1 s.2.1)) f (z,(a,m))) :=
  markedRawEdgeApply_symmetric ν V hZ ψ η d₀ Y Q ρ _ f
    (markedRawFirstGoodCutoff_symmetric r d₀ Y w _ (markedRawMemoryIndependent_symmetric χ)) hf z a

end ArtinMatthews
