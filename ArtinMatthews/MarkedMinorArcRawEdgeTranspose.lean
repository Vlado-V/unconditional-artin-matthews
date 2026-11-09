module

public import ArtinMatthews.MarkedMinorArcRawEdgeFullTranspose
public import ArtinMatthews.MarkedMinorArcRawEdgeJointReverse


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine weighted transpose of the original full physical edge.  Its
reverse stores with V^-1 and promotes with unit charge, keeping the full
joint physical coefficient in its original orientation. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators

theorem markedRawEdgeApply_transpose
    {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (χ f g : MarkedRawState P (pads+1) B Z → ℂ)
    (hχ : ∀ z active, MarkedRawMemorySymmetric (fun m => χ (z,(active,m))))
    (hf : ∀ z active, MarkedRawMemorySymmetric (fun m => f (z,(active,m))))
    (hg : ∀ z active, MarkedRawMemorySymmetric (fun m => g (z,(active,m)))) :
    (∑ s, (markedRawStateMass ν s : ℂ) * g s *
      markedRawEdgeApply ν V hZ ψ η d₀ Y Q ρ χ f s) =
      ∑ s, (markedRawStateMass ν s : ℂ) * f s *
        markedRawEdgeChargedApply ν (fun _ => 1) (fun j => ((V j)⁻¹ : ℝ)) hZ
          (fun target source => markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ χ source target) g s := by
  rw [markedRawEdgeApply_eq_charged]
  apply markedRawEdgeChargedApply_transpose
  · intro z active target m σ
    exact markedRawEdgeJointCoefficient_source_permute hZ ψ η d₀ Y Q ρ χ hχ z active m σ target
  · intro source z active m σ
    exact markedRawEdgeJointCoefficient_target_permute hZ ψ η d₀ Y Q ρ χ hχ source z active m σ
  · exact hf
  · exact hg

end
end ArtinMatthews
