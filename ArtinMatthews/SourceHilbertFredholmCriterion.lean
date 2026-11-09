module

public import OAI.NumberTheory.DirichletL.Eisenstein.FredholmAlternative


set_option backward.privateInPublic true
@[expose] public section

/-! The existing generic compact-estimate criterion with the existential
form used by the source Hilbert-space application. -/

namespace ArtinMatthews.HilbertResolvent

theorem fredholm_of_compact_defect {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (B : E →L[ℂ] E) (hB : IsSelfAdjoint B) (K : E →L[ℂ] F)
    (hK : IsCompactOperator K)
    (hestimate : ∃ A D : ℝ, 0 < A ∧ 0 < D ∧
      ∀ u : E, ‖u‖ ^ 2 ≤ A * ‖B u‖ ^ 2 + D * ‖K u‖ ^ 2) : B.IsFredholm := by
  obtain ⟨A, D, _, _, h⟩ := hestimate
  exact OAI.CubicEisenstein.selfAdjoint_fredholm_of_compact_estimate B hB K hK A D h

end ArtinMatthews.HilbertResolvent
