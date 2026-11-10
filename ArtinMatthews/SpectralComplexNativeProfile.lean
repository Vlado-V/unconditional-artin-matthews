module

public import ArtinMatthews.SpectralNativeHeightProfile
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! A real-valued complex inverse profile with the proved source decay
produces the actual native height datum with exponent five quarters. -/

noncomputable section
open Set
open scoped ContDiff
namespace ArtinMatthews

theorem spectralComplexProfile_native_exists {q w C : ℝ}
    (hq : 0 < q) (hw : 0 < w) (hC : 0 ≤ C) (F : ℝ → ℂ)
    (hF : ContDiffOn ℝ ∞ F (Ioi (0 : ℝ)))
    (hreal : ∀ x, 0 < x → star (F x) = F x)
    (hsmall : ∀ x, 0 < x → ‖F x‖ ≤ C*x^(3/4 : ℝ))
    (hlarge : ∀ x, 1 ≤ x → ‖F x‖ ≤ C/x^2) :
    ∃ P : SpectralDecayingHeightProfile,
      P.exponent = 5/4 ∧
      (∀ y : ℝ, P.value y = Real.sqrt (y/w)*(F ((q/w)*y)).re) ∧
      (∀ x : ℝ, 0 < x → spectralKLHeightPhysicalTest q
        (fun y => P.value (w*y)) x = F x) := by
  let g : ℝ → ℝ := fun x => (F x).re
  have hg : ContDiffOn ℝ ∞ g (Ioi (0 : ℝ)) := by
    intro x hx
    exact Complex.reCLM.contDiff.contDiffAt.comp_contDiffWithinAt x (hF x hx)
  have hnorm (x : ℝ) : ‖g x‖ ≤ ‖F x‖ := by
    simpa only [g,Real.norm_eq_abs] using Complex.abs_re_le_norm (F x)
  have hs (x : ℝ) (hx : 0 < x) : ‖g x‖ ≤ C*x^(3/4 : ℝ) := (hnorm x).trans (hsmall x hx)
  have hl (x : ℝ) (hx : 0 < x) : ‖g x‖ ≤ C*x^(-(3/4 : ℝ)-1) := by
    by_cases hx₁ : x ≤ 1
    · exact (hs x hx).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_ge hx hx₁ (by norm_num)) hC)
    · have hx₁' : 1 ≤ x := le_of_not_ge hx₁
      calc
        _ ≤ C/x^2 := (hnorm x).trans (hlarge x hx₁')
        _ = C*x^(-2 : ℝ) := by rw [Real.rpow_neg hx.le,Real.rpow_two]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hx₁' (by norm_num)) hC
  let P := spectralNativeHeightProfile hq hw (by norm_num : (1/2 : ℝ) < 3/4) hC g hg hs hl
  refine ⟨P,by norm_num [P,spectralNativeHeightProfile],fun y => rfl,?_⟩
  intro x hx
  rw [show spectralKLHeightPhysicalTest q (fun y => P.value (w*y)) x = (g x : ℂ) from
    spectralNativeHeightProfileValue_physical hq hw g hx]
  exact RCLike.conj_eq_iff_re.mp (hreal x hx)

end ArtinMatthews
