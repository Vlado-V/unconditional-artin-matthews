module

public import ArtinMatthews.CircleParameterChoice
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt


set_option backward.privateInPublic true
@[expose] public section

/-! A fixed integer power meets the actual modulus threshold, makes the
finite-detector error negligible, and leaves an arbitrarily small budget
for all polynomially bounded subpower factors. -/

noncomputable section
namespace ArtinMatthews

theorem circle_fixed_power_epsilon_budget {A b u v w ν δ : ℝ}
    (hb : 0 ≤ b) (hA : 2*b+2 ≤ A) (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hν : 0 < ν) (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ δ ∧ ∀ (P : ℝ) (F r : ℕ), 2 ≤ P →
      (F : ℝ) ≤ P^b → (r : ℝ) ≤ P^b →
      4*(F*r) ≤ circlePowerScale P A ∧
        (circlePowerQ P A)^(u*ε) * (r : ℝ)^(v*ε) * P^(w*ε) ≤ P^ν := by
  have hAnonneg : 0 ≤ A := by linarith
  obtain ⟨ε, hε, hεδ, hbudget⟩ := circle_epsilon_budget
    (show 0 ≤ A+3 by linarith) hb hu hv hw hν hδ
  refine ⟨ε, hε, hεδ, fun P F r hP hF hr => ?_⟩
  refine ⟨circlePowerScale_threshold hP hb hA hF hr, ?_⟩
  exact hbudget P (circlePowerQ P A) r (by linarith)
    (by unfold circlePowerQ; positivity) (Nat.cast_nonneg r)
    (circlePowerQ_le hP hAnonneg) hr

theorem circlePowerQ_lower {P A : ℝ} : P^A ≤ circlePowerQ P A := by
  have hc : P^A ≤ (circlePowerScale P A : ℝ) := Nat.le_ceil _
  have hn : (0 : ℝ) ≤ circlePowerScale P A := Nat.cast_nonneg _
  unfold circlePowerQ
  linarith

/-- The two declining ABL powers (`β=1` and `β=1/2`) retain quantitative
decay after every other factor has been bounded by a source-scale power. -/
theorem circlePowerQ_decay {P A B β T : ℝ} (hP : 2 ≤ P) (hβ : 0 ≤ β)
    (hA : B+T ≤ A*β) :
    P^B * (circlePowerQ P A)^(-β) ≤ P^(-T) := by
  have hP0 : 0 < P := by linarith
  have hq := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hP0 A)
    (circlePowerQ_lower (P := P) (A := A)) (neg_nonpos.mpr hβ)
  calc
    _ ≤ P^B * (P^A)^(-β) := mul_le_mul_of_nonneg_left hq (Real.rpow_nonneg hP0.le B)
    _ = P^(B-A*β) := by
      rw [← Real.rpow_mul hP0.le, ← Real.rpow_add hP0]
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)

theorem circlePowerScale_numerator_decay {P A B T E : ℝ} (hP : 2 ≤ P)
    (hA : 2*(B+T) ≤ A) (hE : E ≤ P^B) :
    E / Real.sqrt (circlePowerScale P A) ≤ P^(-T) :=
  (div_le_div_of_nonneg_right hE (Real.sqrt_nonneg _)).trans (circlePowerScale_decay hP hA)

/-- The quantifier order records the needed parameter choice: first a
fixed integer exponent `A`, then a sufficiently small positive `ε`, both
independent of the varying source scale and arithmetic parameters. -/
theorem circle_parameter_choice {b B T u v w ν δ : ℝ}
    (hb : 0 ≤ b) (hB : 0 ≤ B) (hT : 0 ≤ T)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) (hν : 0 < ν) (hδ : 0 < δ) :
    ∃ (A : ℕ) (ε : ℝ), 0 < ε ∧ ε ≤ δ ∧ 2*b+2 ≤ (A : ℝ) ∧
      2*(B+T) ≤ (A : ℝ) ∧ ∀ (P : ℝ) (F r : ℕ), 2 ≤ P →
      (F : ℝ) ≤ P^b → (r : ℝ) ≤ P^b →
      4*(F*r) ≤ circlePowerScale P A ∧
      (circlePowerQ P A)^(u*ε) * (r : ℝ)^(v*ε) * P^(w*ε) ≤ P^ν ∧
      P^B / Real.sqrt (circlePowerScale P A) ≤ P^(-T) := by
  let A : ℕ := ⌈2*b+2+2*(B+T)⌉₊
  have hceil : 2*b+2+2*(B+T) ≤ (A : ℝ) := Nat.le_ceil _
  have hAb : 2*b+2 ≤ (A : ℝ) := by linarith
  have hAB : 2*(B+T) ≤ (A : ℝ) := by linarith
  obtain ⟨ε, hε, hεδ, hbudget⟩ := circle_fixed_power_epsilon_budget hb hAb hu hv hw hν hδ
  refine ⟨A, ε, hε, hεδ, hAb, hAB, fun P F r hP hF hr => ?_⟩
  obtain ⟨hthreshold, hloss⟩ := hbudget P F r hP hF hr
  exact ⟨hthreshold, hloss, circlePowerScale_decay hP hAB⟩

end ArtinMatthews
