module

public import ArtinMatthews.FixedURootFullPowerSaving
public import ArtinMatthews.FixedURootFirstColumns


set_option backward.privateInPublic true
@[expose] public section

/-!
# Uniform root residues

The primitive first-column count in PD (det:root-residue-count), for both
coordinate regimes and every prescribed special-linear residue. The explicit
saving is δ/1000. All interval endpoint choices are retained uniformly.
-/
namespace ArtinMatthews
open Filter
open scoped Topology

/-- Uniform residues of actual primitive roots, with their canonical
completions, at every squarefree subpower modulus. -/
theorem fixedURoot_residue_count {δ : ℝ} (hδ : 0 < δ) (M : ℝ) :
    ∃ E : ℝ, 0 < E ∧ ∀ᶠ x : ℝ in atTop,
      ∀ (S : ℕ) (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S))
        (U V A B α β C D : ℝ) (lcU rcU lcC rcC lcV rcV : Bool),
        x^δ ≤ U → x^δ ≤ V → Squarefree S →
        (S : ℝ) ≤ Real.exp (M*(Real.log x)^(49/50 : ℝ)) →
        U ≤ A → A ≤ B → B ≤ 16*U →
        0 ≤ α → α ≤ β → β ≤ 1 → V ≤ C → C ≤ D → D ≤ 2*V →
        |((fixedURootMatrixFirstColumns g₀ A B α β C D
            lcU rcU lcC rcC lcV rcV).card : ℝ) -
          ((B-A)*(β-α)*(D-C)) /
            ((riemannZeta 2).re *
              (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ))| ≤
          E*U*V*x^(-δ/1000) := by
  obtain ⟨E,hE,hcount⟩ := fixedURootMatrixBox_uniform_power_saving hδ M
  refine ⟨E,hE,?_⟩
  filter_upwards [hcount,eventually_gt_atTop (1:ℝ)] with x hx hx1
  intro S g₀ U V A B α β C D lcU rcU lcC rcC lcV rcV
    hU hV hS hSrange hUA hAB hB hα hαβ hβ hVC hCD hD
  have hA : 1 < A := ((Real.one_lt_rpow hx1 hδ).trans_le hU).trans_le hUA
  have hC : 1 < C := ((Real.one_lt_rpow hx1 hδ).trans_le hV).trans_le hVC
  rw [fixedURootMatrixFirstColumns_card g₀ hA hC hα hβ]
  exact hx S g₀ U V A B α β C D lcU rcU lcC rcC lcV rcV
    hU hV hS hSrange hUA hAB hB hα hαβ hβ hVC hCD hD

end ArtinMatthews
