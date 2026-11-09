module

public import ArtinMatthews.IdealLogCellCount


set_option backward.privateInPublic true
@[expose] public section

/-! The actual discarded-cell mass is small uniformly over growing
finite slot carriers, using their source logarithmic cardinality bound. -/
namespace ArtinMatthews
open Filter
open scoped BigOperators Topology
noncomputable section
attribute [local instance] Classical.propDecidable
universe u

def idealDiscardedThresholdExponent (d H E : ℝ) : ℝ := d+H+2*E+5

theorem idealDiscardedCellMass_uniform (d H E C : ℝ)
    (hd : 0 ≤ d) (hH : 0 ≤ H) :
    ∀ᶠ L : ℝ in atTop, ∀ (I : Type u) [Fintype I] [DecidableEq I],
      ∀ P : I → Finset ℕ, (∀ i p, p ∈ P i → p.Prime) →
      (∀ i p, p ∈ P i → (p : ℝ) ≤ Real.exp (L^d)) →
      (Fintype.card I : ℝ) ≤ C*Real.log L →
      idealDiscardedCellMass P (L^(-H)) (L^(-idealDiscardedThresholdExponent d H E)) ≤
        L^(-2*E-2) := by
  filter_upwards [eventually_ge_atTop (max 2 C)] with L hlarge
  have hL2 : 2 ≤ L := (le_max_left _ _).trans hlarge
  have hL1 : 1 ≤ L := by linarith
  have hL : 0 < L := by linarith
  have hCL : C ≤ L := (le_max_right _ _).trans hlarge
  intro I _ _ P hP hupper hcard
  have hc : (Fintype.card I : ℝ) ≤ L^2 := by
    calc
      _ ≤ C*Real.log L := hcard
      _ ≤ L*L := mul_le_mul hCL (Real.log_le_self hL.le) (Real.log_nonneg hL1) hL.le
      _ = _ := (pow_two _).symm
  have hcount : 1+(Fintype.card I : ℝ)*L^d/L^(-H) ≤ L^(d+H+3) := by
    calc
      _ ≤ 1+L^2*L^d/L^(-H) := by
        have hz := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hL.le d)) (Real.rpow_nonneg hL.le (-H))
        linarith
      _ = 1+L^(d+H+2) := by
        rw [← Real.rpow_two, ← Real.rpow_add hL, ← Real.rpow_sub hL]
        congr 2
        ring
      _ ≤ 2*L^(d+H+2) := by
        have hp := Real.one_le_rpow hL1 (show 0 ≤ d+H+2 by linarith)
        linarith
      _ ≤ L*L^(d+H+2) := mul_le_mul_of_nonneg_right hL2 (Real.rpow_nonneg hL.le _)
      _ = _ := by nth_rw 1 [← Real.rpow_one L]; rw [← Real.rpow_add hL]; congr 1; ring
  calc
    _ ≤ (1+(Fintype.card I : ℝ)*L^d/L^(-H))*L^(-idealDiscardedThresholdExponent d H E) :=
      idealDiscardedCellMass_source_le P hP (Real.rpow_nonneg hL.le _) (Real.rpow_pos_of_pos hL _)
        (Real.rpow_nonneg hL.le _) hupper
    _ ≤ L^(d+H+3)*L^(-idealDiscardedThresholdExponent d H E) :=
      mul_le_mul_of_nonneg_right hcount (Real.rpow_nonneg hL.le _)
    _ = _ := by
      rw [← Real.rpow_add hL]
      congr 1
      dsimp [idealDiscardedThresholdExponent]
      ring

end
end ArtinMatthews
