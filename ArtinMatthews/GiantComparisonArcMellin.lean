module

public import ArtinMatthews.GiantComparisonNatFourier
public import ArtinMatthews.SourceAdditiveMellinScale
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

/-! A real arc centered at any point is the literal PD 6.4 energy
for the phase-twisted endpoint coefficients. -/
namespace ArtinMatthews
open MeasureTheory AddCircle Set
open scoped BigOperators
noncomputable section
local instance : Fact (0 < (1:ℝ)) := ⟨by norm_num⟩
local notation "Circle1" => AddCircle (1:ℝ)
local notation "e" => OAI.Problem337.RealPhase.phase

def giantComparisonArcTwist (r : ℝ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  a n*e (r*(n:ℝ))

theorem giantComparisonArcTwist_norm (r : ℝ) (a : ℕ → ℂ) (n : ℕ) :
    ‖giantComparisonArcTwist r a n‖ = ‖a n‖ := by
  rw [giantComparisonArcTwist,norm_mul,OAI.Problem337.RealPhase.norm_phase,mul_one]

theorem giantComparisonNatFourier_shift (S : Finset ℕ) (a : ℕ → ℂ) (r β : ℝ) :
    giantComparisonNatFourier S a ((β+r:ℝ):Circle1) =
      sourceLocalAdditivePolynomial S (fun n => (n:ℝ)) (giantComparisonArcTwist r a) β := by
  rw [giantComparisonNatFourier_apply,sourceLocalAdditivePolynomial]
  apply Finset.sum_congr rfl
  intro n _
  rw [show (β+r)*(n:ℝ)=r*(n:ℝ)+β*(n:ℝ) by ring,OAI.Problem337.RealPhase.phase_add]
  simp only [giantComparisonArcTwist,mul_assoc]

theorem giantComparisonNatFourier_arc_energy_eq (S : Finset ℕ) (a : ℕ → ℂ)
    (r : ℝ) {H : ℝ} (hH : 0 < H) :
    (∫ t in Icc (r-H⁻¹) (r+H⁻¹), ‖giantComparisonNatFourier S a (t:Circle1)‖^2) =
      ∫ β in Icc (-H⁻¹) H⁻¹,
        ‖sourceLocalAdditivePolynomial S (fun n => (n:ℝ)) (giantComparisonArcTwist r a) β‖^2 := by
  let F (t : ℝ) := ‖giantComparisonNatFourier S a (t:Circle1)‖^2
  have h₀ : -H⁻¹ ≤ H⁻¹ := by linarith [inv_pos.mpr hH]
  have hr : r-H⁻¹ ≤ r+H⁻¹ := by linarith
  calc
    _ = ∫ t in (r-H⁻¹)..(r+H⁻¹), F t := by
      rw [intervalIntegral.integral_of_le hr,integral_Icc_eq_integral_Ioc]
    _ = ∫ β in (-H⁻¹)..H⁻¹, F (β+r) := by
      symm
      simpa only [show -H⁻¹+r=r-H⁻¹ by ring,add_comm H⁻¹ r] using
        intervalIntegral.integral_comp_add_right (a := -H⁻¹) (b := H⁻¹) F r
    _ = ∫ β in Icc (-H⁻¹) H⁻¹, F (β+r) := by
      rw [intervalIntegral.integral_of_le h₀,integral_Icc_eq_integral_Ioc]
    _ = _ := by simp only [F,giantComparisonNatFourier_shift]

/-- Apply the checked source Mellin energy estimate to a translated arc.
The scale and the spectral density retain their literal PD 6.4 normalization. -/
theorem giantComparisonNatFourier_arc_energy_le
    (c C : ℝ) (hc : 0 < c) (hcC : c ≤ C) (j : ℕ) (hj : 2 ≤ j) :
    ∃ K > 0, ∀ (S : Finset ℕ) (a : ℕ → ℂ) (r Y H : ℝ), 0 < Y → 0 < H → H ≤ Y →
      (∀ n ∈ S, (n:ℝ) ∈ Icc (c*Y) (C*Y)) →
      (∫ t in Icc (r-H⁻¹) (r+H⁻¹), ‖giantComparisonNatFourier S a (t:Circle1)‖^2) ≤
        K*(Y⁻¹*∫ t : ℝ, sourceLocalMellinEnergyDensity S (fun n => (n:ℝ))
          (giantComparisonArcTwist r a) Y H j t) := by
  obtain ⟨K,hK,h⟩ := sourceAdditiveMellinEnergy_real c C hc hcC j hj
  refine ⟨K,hK,?_⟩
  intro S a r Y H hY hH hHY hS
  rw [giantComparisonNatFourier_arc_energy_eq S a r hH]
  exact h S (fun n => (n:ℝ)) (giantComparisonArcTwist r a) Y H hY hH hHY hS

end
end ArtinMatthews
