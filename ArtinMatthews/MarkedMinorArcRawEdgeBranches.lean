module

public import ArtinMatthews.MarkedMinorArcRawEdgeClean


set_option backward.privateInPublic true
@[expose] public section

/-! Literal finite clean/dirty partition of the full store/promote edge
choices. The clean branch is identified with the proved raw clean action. -/
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Clean means that no source group is stored and no old index promoted. -/
def MarkedRawEdgeChoiceClean {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    {hZ : ∀ z ∈ Z, IsCoprime z.1 z.2} {s : MarkedRawState P (pads+1) B Z}
    (choice : MarkedRawEdgeChoice hZ s) : Prop :=
  (∀ j, choice.store j=false) ∧ (∀ j, choice.promotions j=none)

/-- Every clean choice is exactly a counting target and one actual fresh
prime per group, without any leftover redundant prime or index choices. -/
def markedRawCleanEdgeChoiceEquiv {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z) :
    {choice : MarkedRawEdgeChoice hZ s // MarkedRawEdgeChoiceClean choice} ≃
      Z × ((j : J) → ↥(P j)) where
  toFun choice := (choice.1.target,markedRawEdgeTargetLast s.2.2 choice.1.promotions choice.1.fresh)
  invFun pair := ⟨markedRawCleanEdgeChoice hZ s pair.1 pair.2,⟨fun _ => rfl,fun _ => rfl⟩⟩
  left_inv choice := by
    apply Subtype.ext
    rcases choice with ⟨⟨target,store,prom,fresh,hh,hb⟩,hc⟩
    have hs : store=(fun _ => false) := funext hc.1
    have hp : prom=(fun _ => none) := funext hc.2
    cases hs
    cases hp
    rfl
  right_inv pair := rfl

/-- Exact summand of the literal full raw edge action. -/
noncomputable def markedRawEdgeSummand {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (f : MarkedRawState P (pads+1) B Z → ℂ) (s : MarkedRawState P (pads+1) B Z)
    (choice : MarkedRawEdgeChoice hZ s) : ℂ :=
  (markedRawEdgeChoicePrimeMass ν V hZ s choice : ℂ)*
    markedRawEdgeChoiceCoefficient hZ ψ η d₀ Y Q ρ χ s choice*
      f (markedRawEdgeTargetState hZ s choice)

/-- The sum over literal clean edge choices is exactly the banned raw
clean action used in the unconditional clean operator bound. -/
theorem markedRawEdge_clean_sum {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (f : MarkedRawState P (pads+1) B Z → ℂ) (s : MarkedRawState P (pads+1) B Z) :
    (∑ choice : {choice : MarkedRawEdgeChoice hZ s // MarkedRawEdgeChoiceClean choice},
      markedRawEdgeSummand ν V hZ ψ η d₀ Y Q ρ χ f s choice.1)=
      markedRawCleanApply ν (markedRawBannedCleanKernel (markedRawCleanKernel hZ ψ η d₀ Y Q ρ χ)) f s := by
  classical
  rw [← Equiv.sum_comp (markedRawCleanEdgeChoiceEquiv hZ s).symm]
  rw [Fintype.sum_prod_type]
  unfold markedRawCleanApply
  apply Finset.sum_congr rfl
  intro target _
  apply Finset.sum_congr rfl
  intro fresh _
  change (markedRawEdgeChoicePrimeMass ν V hZ s (markedRawCleanEdgeChoice hZ s target fresh) : ℂ)*
    markedRawEdgeChoiceCoefficient hZ ψ η d₀ Y Q ρ χ s (markedRawCleanEdgeChoice hZ s target fresh)*
    f (markedRawEdgeTargetState hZ s (markedRawCleanEdgeChoice hZ s target fresh))=_
  rw [markedRawCleanEdgeChoice_prime_mass,markedRawCleanEdgeChoice_coefficient,markedRawCleanEdgeChoice_target]

/-- Exact partition of the full literal signed edge row into its actual
clean action and the sum over actual store-or-promote choices. -/
theorem markedRawEdgeApply_eq_clean_add_dirty {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (f : MarkedRawState P (pads+1) B Z → ℂ) (s : MarkedRawState P (pads+1) B Z) :
    markedRawEdgeApply ν V hZ ψ η d₀ Y Q ρ χ f s=
      markedRawCleanApply ν (markedRawBannedCleanKernel (markedRawCleanKernel hZ ψ η d₀ Y Q ρ χ)) f s+
      ∑ choice : {choice : MarkedRawEdgeChoice hZ s // ¬MarkedRawEdgeChoiceClean choice},
        markedRawEdgeSummand ν V hZ ψ η d₀ Y Q ρ χ f s choice.1 := by
  classical
  rw [← markedRawEdge_clean_sum ν V]
  change (∑ choice : MarkedRawEdgeChoice hZ s, markedRawEdgeSummand ν V hZ ψ η d₀ Y Q ρ χ f s choice)=_
  exact (Fintype.sum_subtype_add_sum_subtype MarkedRawEdgeChoiceClean
    (markedRawEdgeSummand ν V hZ ψ η d₀ Y Q ρ χ f s)).symm

end ArtinMatthews
