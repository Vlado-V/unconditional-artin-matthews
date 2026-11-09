module

public import ArtinMatthews.FixedURootPrescribedMatrix
public import ArtinMatthews.FixedURootPowerSaving


set_option backward.privateInPublic true
@[expose] public section

/-! The actual power-saving root-box theorem stated for a prescribed
special-linear matrix, rather than a chosen tuple of integer lifts. -/
namespace ArtinMatthews
open Filter
open scoped Topology

/-- Uniform prescribed-matrix root residues in the smaller-first-coordinate regime. -/
theorem fixedURootMatrixBox_power_saving {δ : ℝ} (hδ : 0 < δ) (M : ℝ) :
    ∃ E : ℝ, 0 < E ∧ ∀ᶠ x : ℝ in atTop,
      ∀ (S : ℕ) (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S))
        (U V A B α β C D : ℝ) (lcU rcU lcC rcC lcV rcV : Bool),
        x^δ ≤ U → U ≤ V → Squarefree S →
        (S : ℝ) ≤ Real.exp (M*(Real.log x)^(49/50 : ℝ)) →
        U ≤ A → A ≤ B → B ≤ 16*U →
        0 ≤ α → α ≤ β → β ≤ 1 → C ≤ D → D-C ≤ V →
        |((fixedURootMatrixBoxPoints g₀ A B α β C D
            lcU rcU lcC rcC lcV rcV).card : ℝ) -
          ((B-A)*(β-α)*(D-C)) /
            ((riemannZeta 2).re *
              (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ))| ≤
          E*U*V*x^(-δ/1000) := by
  obtain ⟨E,hE,hcount⟩ := fixedURootBox_power_saving hδ M
  refine ⟨E,hE,?_⟩
  filter_upwards [hcount] with x hx
  intro S g₀ U V A B α β C D lcU rcU lcC rcC lcV rcV
    hU hUV hS hSrange hUA hAB hB hα hαβ hβ hCD hY
  let : NeZero S := ⟨hS.ne_zero⟩
  exact hx S (fixedURootMatrixEntry g₀ 0 0) (fixedURootMatrixEntry g₀ 0 1)
    (fixedURootMatrixEntry g₀ 1 0) (fixedURootMatrixEntry g₀ 1 1)
    U V A B α β C D lcU rcU lcC rcC lcV rcV hU hUV hS hSrange
    (fixedURootMatrixEntry_det g₀) hUA hAB hB hα hαβ hβ hCD hY

end ArtinMatthews
