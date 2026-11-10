module

public import ArtinMatthews.CircleDetector
public import ArtinMatthews.CircleNormalizerDefinitions
public import ArtinMatthews.CircleNormalizer
public import ArtinMatthews.CircleNormalizerMass
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

/-! The finite detector error decays at a quantitative power of the actual
modulus scale. The admissible family and smooth weights are unchanged. -/

noncomputable section
namespace ArtinMatthews

theorem circleDetector_error_rate (ε : ℝ) (hε : 0<ε) (hεone : ε≤1) :
    ∃ C : ℝ, 0<C ∧ ∀ F r L : ℕ, 0<F → 0<r → F.Coprime r →
      4*(F*r)≤L → ∀ (ω : ℕ → ℝ) (W : ℝ), 0≤W →
      (∀ q∈circleModuli F r L, 0≤ω q) →
      (∀ q∈circleModuli F r L, ω q≤W) →
      (∀ q : ℕ, 4*L≤q → q≤5*L → 1≤ω q) → ∀ R : ℕ,
      circleWeightMass (circleModuli F r L) ω*(R : ℝ)^2 /
          circleNormalizer (circleModuli F r L) ω ≤
        C*W*(F : ℝ)*(r : ℝ)^ε*(R : ℝ)^2*(L : ℝ)^(ε-1) := by
  obtain ⟨c,hc,hlower⟩ := circleNormalizer_lower ε hε hεone
  refine ⟨4/c,by positivity,?_⟩
  intro F r L hF hr hFr hL ω W hW hω hupper hplateau R
  have hLpos : 0<L := lt_of_lt_of_le (by positivity : 0<4*(F*r)) hL
  have hLR : (0 : ℝ)<L := by exact_mod_cast hLpos
  have hFR : (0 : ℝ)<F := by exact_mod_cast hF
  have hrR : (0 : ℝ)<r := by exact_mod_cast hr
  have hΛ := circleNormalizer_positive hF hr hFr hL ω hω hplateau
  have hl := hlower F r L hF hr hFr hL ω hω hplateau
  have hlpos : 0<c*(L : ℝ)^(2-ε)/((F : ℝ)*(r : ℝ)^ε) := by positivity
  have hm := circleModuli_weightMass_le F r L hLpos ω W hW hupper
  calc
    _ ≤ (4*W*(L : ℝ)*(R : ℝ)^2) / circleNormalizer (circleModuli F r L) ω :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hm (sq_nonneg _)) hΛ.le
    _ ≤ (4*W*(L : ℝ)*(R : ℝ)^2) / (c*(L : ℝ)^(2-ε)/((F : ℝ)*(r : ℝ)^ε)) :=
      div_le_div_of_nonneg_left (by positivity) hlpos hl
    _ = _ := by
      have hp : (L : ℝ)^(2-ε)=(L : ℝ)/(L : ℝ)^(ε-1) := by
        calc
          _ = (L : ℝ)^(1+(-(ε-1))) := by congr 1; ring
          _ = _ := by rw [Real.rpow_add hLR,Real.rpow_one,Real.rpow_neg hLR.le]; ring
      rw [hp]
      field_simp

theorem circleDetector_error_sqrt (ε : ℝ) (hε : 0<ε) (hεhalf : ε≤1/2) :
    ∃ C : ℝ, 0<C ∧ ∀ F r L : ℕ, 0<F → 0<r → F.Coprime r →
      4*(F*r)≤L → ∀ (ω : ℕ → ℝ) (W : ℝ), 0≤W →
      (∀ q∈circleModuli F r L, 0≤ω q) →
      (∀ q∈circleModuli F r L, ω q≤W) →
      (∀ q : ℕ, 4*L≤q → q≤5*L → 1≤ω q) → ∀ R : ℕ,
      circleWeightMass (circleModuli F r L) ω*(R : ℝ)^2 /
          circleNormalizer (circleModuli F r L) ω ≤
        C*W*(F : ℝ)*(r : ℝ)*(R : ℝ)^2/Real.sqrt L := by
  obtain ⟨C,hC,hbound⟩ := circleDetector_error_rate ε hε (by linarith)
  refine ⟨C,hC,?_⟩
  intro F r L hF hr hFr hL ω W hW hω hupper hplateau R
  have hLpos : 0<L := lt_of_lt_of_le (by positivity : 0<4*(F*r)) hL
  have hLone : (1 : ℝ)≤L := by exact_mod_cast hLpos
  have hrone : (1 : ℝ)≤r := by exact_mod_cast hr
  have hrpow : (r : ℝ)^ε≤r := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hrone (show ε≤1 by linarith)
  have hLpow : (L : ℝ)^(ε-1)≤(L : ℝ)^(-(1/2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hLone (by linarith)
  calc
    _ ≤ C*W*(F : ℝ)*(r : ℝ)^ε*(R : ℝ)^2*(L : ℝ)^(ε-1) :=
      hbound F r L hF hr hFr hL ω W hW hω hupper hplateau R
    _ ≤ C*W*(F : ℝ)*(r : ℝ)*(R : ℝ)^2*(L : ℝ)^(-(1/2 : ℝ)) := by
      apply mul_le_mul _ hLpow (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hrpow (by positivity)) (sq_nonneg _)
    _ = _ := by rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ L),← Real.sqrt_eq_rpow]; ring

end ArtinMatthews
