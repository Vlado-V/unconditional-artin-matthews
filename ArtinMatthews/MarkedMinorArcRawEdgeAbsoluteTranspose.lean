module

public import ArtinMatthews.MarkedMinorArcRawEdgeTranspose


set_option backward.privateInPublic true
@[expose] public section

/-! The exact absolute edge transpose.  Its coefficients are the norms of
the original physical coefficients, and its reverse charges are obtained
from the literal factorial change of variables. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators

def markedRawEdgeAbsApply
    {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (χ f : MarkedRawState P (pads+1) B Z → ℂ)
    (s : MarkedRawState P (pads+1) B Z) : ℂ :=
  ∑ c : MarkedRawEdgeChoice hZ s, (markedRawEdgeChoicePrimeMass ν V hZ s c : ℂ) *
    (‖markedRawEdgeChoiceCoefficient hZ ψ η d₀ Y Q ρ χ s c‖ : ℂ) *
      f (markedRawEdgeTargetState hZ s c)

theorem markedRawEdgeAbsApply_eq_charged
    {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (χ f : MarkedRawState P (pads+1) B Z → ℂ) :
    markedRawEdgeAbsApply ν V hZ ψ η d₀ Y Q ρ χ f =
      markedRawEdgeChargedApply ν (fun j => ((V j)⁻¹ : ℝ)) (fun _ => 1) hZ
        (fun s t => (‖markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ χ s t‖ : ℂ)) f := by
  funext s
  unfold markedRawEdgeAbsApply markedRawEdgeChargedApply
  apply Finset.sum_congr rfl
  intro c _
  rw [markedRawEdgeChoiceCharge_original, markedRawEdgeChoiceCoefficient_eq_joint]

theorem markedRawEdgeAbsApply_transpose
    {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (χ f g : MarkedRawState P (pads+1) B Z → ℂ)
    (hχ : ∀ z active, MarkedRawMemorySymmetric (fun m => χ (z,(active,m))))
    (hf : ∀ z active, MarkedRawMemorySymmetric (fun m => f (z,(active,m))))
    (hg : ∀ z active, MarkedRawMemorySymmetric (fun m => g (z,(active,m)))) :
    (∑ s, (markedRawStateMass ν s : ℂ) * g s *
      markedRawEdgeAbsApply ν V hZ ψ η d₀ Y Q ρ χ f s) =
      ∑ s, (markedRawStateMass ν s : ℂ) * f s *
        markedRawEdgeChargedApply ν (fun _ => 1) (fun j => ((V j)⁻¹ : ℝ)) hZ
          (fun target source => (‖markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ χ source target‖ : ℂ)) g s := by
  rw [markedRawEdgeAbsApply_eq_charged]
  apply markedRawEdgeChargedApply_transpose
  · intro z active target m σ
    exact congrArg (fun u : ℂ => (‖u‖ : ℂ))
      (markedRawEdgeJointCoefficient_source_permute hZ ψ η d₀ Y Q ρ χ hχ z active m σ target)
  · intro source z active m σ
    exact congrArg (fun u : ℂ => (‖u‖ : ℂ))
      (markedRawEdgeJointCoefficient_target_permute hZ ψ η d₀ Y Q ρ χ hχ source z active m σ)
  · exact hf
  · exact hg

end
end ArtinMatthews
