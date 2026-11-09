module

public import ArtinMatthews.ShiftedABLMellinCircle


set_option backward.privateInPublic true
@[expose] public section

/-! The exact pointwise signed spectral input consumed by source
correlation. The unrestricted Mellin heights have a fixed polynomial cost. -/

noncomputable section
open OAI OAI.SevenEighths
open scoped BigOperators
namespace ArtinMatthews

def ShiftedABLSignedSpectralInput : Prop :=
  ∀ B ν : ℝ, 0 < B → 0 < ν → ∃ (J : ℕ) (C : ℝ), 0 < C ∧
    ∀ (χ : HeckeFamily.Character) (D m3 m4 F L : ℕ) [NeZero F] [NeZero D],
      0 < m3 → 0 < m4 → m3 ≠ m4 → (m3*m4).Coprime F → 0 < L →
      (F : ℝ) ≤ 3*(L : ℝ) → ∀ (d : ℕ × ℕ) (i : ℕ × Bool),
      let r := m3*m4
      let n := shiftedABLFirstIndex m3 m4
      let R : ℝ := 2^i.1
      let Q : ℝ := 3*(L : ℝ)
      let X := Real.sqrt (R*(n : ℝ))/(Real.sqrt (r : ℝ)*Q)
      let G := Real.sqrt ((n : ℝ)*(((r*F).gcd n : ℕ) : ℝ))
      let P₀ := Q*R*(n : ℝ)*(r : ℝ)
      X ≤ B → ∀ V : ℝ, 1 ≤ V → (n : ℝ)*X ≤ V*G → ∀ z : ℝ × ℝ,
      ‖shiftedABLMellinSignedSum χ D m3 m4 F r L d i z‖ ≤
        C*(F : ℝ)*Real.sqrt r*P₀^ν*Real.sqrt V*(1+|z.1|+|z.2|)^J *
          Real.sqrt (∑ ρ ∈ (shiftedABLDualFrequencies m3 m4 d).filter
            (fun ρ => shiftedABLSignedFrequencyIndex ρ=i),
            ‖shiftedABLMellinRhoCoefficient χ D m3 m4 d ρ z‖^2) *
          Real.sqrt (1+R/((r : ℝ)*(F : ℝ))) *
          Real.sqrt (1+G/(X*(r : ℝ)*(F : ℝ)))

end ArtinMatthews
