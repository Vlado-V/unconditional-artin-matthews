module

public import ArtinMatthews.MarkedMinorArcRawEdgeChargedRow


set_option backward.privateInPublic true
@[expose] public section

/-! The reverse joint kernel on each actual indexed edge is the forward
kernel with reflected Schwartz cutoff. This preserves the literal row. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators

theorem markedRawEdgeJointCoefficient_target_norm_reverse
    {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hdisj : Pairwise (fun i j => Disjoint (P i) (P j)))
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (s : MarkedRawState P (pads+1) B Z) (c : MarkedRawEdgeChoice hZ s) :
    ‖markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ χ (markedRawEdgeTargetState hZ s c) s‖ =
      ‖markedRawEdgeJointCoefficient hZ (markedRawEdgeReflectedCutoff ψ) η d₀ Y Q ρ χ
        s (markedRawEdgeTargetState hZ s c)‖ := by
  let copied := ((markedRawActiveSplit pads) s.2.1).1
  let a := ((markedRawActiveSplit pads) s.2.1).2
  let b := markedRawEdgeTargetLast s.2.2 c.promotions c.fresh
  have hs : (s.1,((markedRawActiveSplit pads).symm (copied,a),s.2.2)) = s := by
    change (s.1,((markedRawActiveSplit pads).symm ((markedRawActiveSplit pads) s.2.1),s.2.2)) = s
    rw [Equiv.symm_apply_apply]
  have hh := markedRawEdgeJointCoefficient_norm_reverse hdisj hZ ψ η d₀ Y Q ρ χ
    copied c.target s.1 b a (markedRawEdgeTargetMemory hZ s c) s.2.2
  rw [hs] at hh
  exact hh

theorem markedRawEdgeChargedWeightedAbsRow_reverse_eq
    {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (δ γ : J → ℂ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hdisj : Pairwise (fun i j => Disjoint (P i) (P j)))
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ v₀ : ℝ) (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (s : MarkedRawState P (pads+1) B Z) (modifier : MarkedRawEdgeChoice hZ s → ℂ) :
    markedRawEdgeChargedWeightedAbsRow ν δ γ hZ
      (fun t u => markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ χ u t) v₀ s modifier =
      markedRawEdgeChargedWeightedAbsRow ν δ γ hZ
        (markedRawEdgeJointCoefficient hZ (markedRawEdgeReflectedCutoff ψ) η d₀ Y Q ρ χ)
        v₀ s modifier := by
  classical
  unfold markedRawEdgeChargedWeightedAbsRow
  apply Finset.sum_congr rfl
  intro c _
  simp only [norm_mul]
  rw [markedRawEdgeJointCoefficient_target_norm_reverse hdisj hZ ψ η d₀ Y Q ρ χ s c]

end
end ArtinMatthews
