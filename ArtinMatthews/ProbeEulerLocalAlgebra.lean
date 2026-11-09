module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic


set_option backward.privateInPublic true
@[expose] public section

/-! Exact algebra of the good-prime rational factor in source05.
The identification with the finite local Gauss sum is a separate step. -/

namespace ArtinMatthews

noncomputable section

def probeGoodLocalFactor (Q V W D E : ℂ) : ℂ :=
  1 / (1 - V) + W / (1 - W) +
    E / (1 - E) * ((1 - Q⁻¹) / (1 - V) + W) -
    D / (1 - E) * (1 + (Q - 1) * W * V / (1 - V))

def probeGoodLocalCorrection (Q V W D E : ℂ) : ℂ :=
  (1 - V) * (1 - W) / (1 - D) * probeGoodLocalFactor Q V W D E

def probeGoodLocalErrorNumerator (Q V W D : ℂ) : ℂ :=
  D * (W + V - W * V) - W * V - (Q - 1) * D * (1 - W) * W * V

def probeGoodLocalGeometricNumerator (Q V W D : ℂ) : ℂ :=
  (1 - D) - (1 - W) * Q⁻¹ - W ^ 2 * (1 - V)

theorem probeGoodLocalCorrection_sub_one (Q V W D E : ℂ)
    (hQ : Q ≠ 0) (hV : 1 - V ≠ 0) (hW : 1 - W ≠ 0)
    (hD : 1 - D ≠ 0) (hE : 1 - E ≠ 0) :
    probeGoodLocalCorrection Q V W D E - 1 =
      (probeGoodLocalErrorNumerator Q V W D +
        E * probeGoodLocalGeometricNumerator Q V W D) / ((1 - D) * (1 - E)) := by
  unfold probeGoodLocalCorrection probeGoodLocalFactor
    probeGoodLocalErrorNumerator probeGoodLocalGeometricNumerator
  field_simp
  ring

theorem probeGoodLocalCorrection_zero_geometric (Q V W D : ℂ)
    (hQ : Q ≠ 0) (hV : 1 - V ≠ 0) (hW : 1 - W ≠ 0)
    (hD : 1 - D ≠ 0) :
    probeGoodLocalCorrection Q V W D 0 - 1 =
      probeGoodLocalErrorNumerator Q V W D / (1 - D) := by
  simpa using probeGoodLocalCorrection_sub_one Q V W D 0 hQ hV hW hD (by norm_num)

theorem probe_one_sub_norm_lower {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    1 / 2 ≤ ‖1 - z‖ := by
  have h := norm_sub_norm_le (1 : ℂ) z
  norm_num at h
  linarith

theorem probe_one_sub_ne_zero {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) : 1 - z ≠ 0 := by
  exact norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) (probe_one_sub_norm_lower hz))

end

end ArtinMatthews
