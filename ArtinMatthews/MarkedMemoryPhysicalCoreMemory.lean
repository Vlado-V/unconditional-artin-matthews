module

public import ArtinMatthews.MarkedMemoryCopiedSlotGeometry


set_option backward.privateInPublic true
@[expose] public section

/-! At rho=1 the actual joint edge coefficient has no pending-memory
factor. Its physical core is therefore unchanged by pending enumeration;
position-only multipliers are retained exactly. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
  {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
  (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q : ℝ)

theorem markedRawEdgeJointCoefficient_one_memory
    (x y : Z) (a b : MarkedRawActive P (pads+1))
    (m₁ m₂ n₁ n₂ : MarkedRawMemory P B) :
    markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q 1 (fun _ => 1) (x,(a,m₁)) (y,(b,n₁)) =
      markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q 1 (fun _ => 1) (x,(a,m₂)) (y,(b,n₂)) := by
  unfold markedRawEdgeJointCoefficient markedRawEndpointFactor
  simp only [one_pow,Complex.ofReal_one,one_mul]

theorem markedRawEdgeJointCoefficient_one_state_ext
    (s₁ s₂ t₁ t₂ : MarkedRawState P (pads+1) B Z)
    (hsp : s₁.1=s₂.1) (hsa : s₁.2.1=s₂.2.1)
    (htp : t₁.1=t₂.1) (hta : t₁.2.1=t₂.2.1) :
    markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q 1 (fun _ => 1) s₁ t₁ =
      markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q 1 (fun _ => 1) s₂ t₂ := by
  rcases s₁ with ⟨x,a,m₁⟩
  rcases s₂ with ⟨x',a',m₂⟩
  rcases t₁ with ⟨y,b,n₁⟩
  rcases t₂ with ⟨y',b',n₂⟩
  cases hsp
  cases hsa
  cases htp
  cases hta
  exact markedRawEdgeJointCoefficient_one_memory hZ ψ η d₀ Y Q _ _ _ _ _ _ _ _

theorem markedRawEdgeJointCoefficient_one_positionTest
    (F : Z → ℂ) (s₁ s₂ t₁ t₂ : MarkedRawState P (pads+1) B Z)
    (hsp : s₁.1=s₂.1) (hsa : s₁.2.1=s₂.2.1)
    (htp : t₁.1=t₂.1) (hta : t₁.2.1=t₂.2.1) :
    markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q 1 (fun s => F s.1) s₁ t₁ =
      markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q 1 (fun s => F s.1) s₂ t₂ := by
  rw [markedRawEdgeJointCoefficient_test_factor hZ ψ η d₀ Y Q 1 (fun s => F s.1) s₁ t₁,
    markedRawEdgeJointCoefficient_test_factor hZ ψ η d₀ Y Q 1 (fun s => F s.1) s₂ t₂,
    markedRawEdgeJointCoefficient_one_state_ext hZ ψ η d₀ Y Q s₁ s₂ t₁ t₂ hsp hsa htp hta,
    hsp,htp]

end
end ArtinMatthews
