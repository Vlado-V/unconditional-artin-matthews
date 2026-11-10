module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! Actual square-root radial substitution for the Gaussian transform of
the Weyl kernel, with exact Jacobian and integrability equivalence. -/

noncomputable section
open Set MeasureTheory

namespace ArtinMatthews

def spectralWeylRadius (A u : ℝ) : ℝ := Real.sqrt (A+u^2)

theorem spectralWeylRadius_pos {A : ℝ} (hA : 0 < A) (u : ℝ) :
    0 < spectralWeylRadius A u := Real.sqrt_pos.mpr (by nlinarith [sq_nonneg u])

theorem spectralWeylRadius_sq {A : ℝ} (hA : 0 < A) (u : ℝ) :
    spectralWeylRadius A u ^ 2 = A+u^2 := Real.sq_sqrt (by nlinarith [sq_nonneg u])

theorem spectralWeylRadius_hasDerivAt {A : ℝ} (hA : 0 < A) (u : ℝ) :
    HasDerivAt (spectralWeylRadius A) (u/spectralWeylRadius A u) u := by
  have hd := (Real.hasDerivAt_sqrt (by nlinarith [sq_nonneg u] : A+u^2 ≠ 0)).comp u
    (((hasDerivAt_id u).pow 2).const_add A)
  convert hd using 1
  · rfl
  · dsimp [spectralWeylRadius]
    field_simp

theorem spectralWeylRadius_image {A : ℝ} (hA : 0 < A) :
    spectralWeylRadius A '' Ioi (0 : ℝ) = Ioi (Real.sqrt A) := by
  ext X
  constructor
  · rintro ⟨u,hu,rfl⟩
    change 0 < u at hu
    change Real.sqrt A < Real.sqrt (A+u^2)
    exact (Real.sqrt_lt_sqrt_iff hA.le).mpr (by nlinarith [sq_pos_of_pos hu])
  · intro hX
    change Real.sqrt A < X at hX
    have hX0 : 0 < X := (Real.sqrt_nonneg A).trans_lt hX
    have hr : 0 < X^2-A := by
      have hm := mul_pos (sub_pos.mpr hX) (add_pos_of_pos_of_nonneg hX0 (Real.sqrt_nonneg A))
      nlinarith [Real.sq_sqrt hA.le]
    refine ⟨Real.sqrt (X^2-A),Real.sqrt_pos.mpr hr,?_⟩
    unfold spectralWeylRadius
    rw [Real.sq_sqrt hr.le,add_sub_cancel,Real.sqrt_sq hX0.le]

theorem spectralWeylRadius_injOn {A : ℝ} (hA : 0 < A) :
    InjOn (spectralWeylRadius A) (Ioi (0 : ℝ)) := by
  intro u hu v hv huv
  change 0 < u at hu
  change 0 < v at hv
  have hsq := congrArg (fun r : ℝ => r^2) huv
  rw [spectralWeylRadius_sq hA,spectralWeylRadius_sq hA] at hsq
  nlinarith

theorem spectralWeylRadius_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : ℝ} (hA : 0 < A) (F : ℝ → E) :
    (∫ X in Ioi (Real.sqrt A), F X) =
      ∫ u in Ioi (0 : ℝ), (u/spectralWeylRadius A u) • F (spectralWeylRadius A u) := by
  rw [← spectralWeylRadius_image hA]
  rw [integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun u _ => (spectralWeylRadius_hasDerivAt hA u).hasDerivWithinAt)
    (spectralWeylRadius_injOn hA)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  dsimp only
  rw [abs_of_pos (div_pos hu (spectralWeylRadius_pos hA u))]

theorem spectralWeylRadius_integrable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : ℝ} (hA : 0 < A) (F : ℝ → E) :
    IntegrableOn F (Ioi (Real.sqrt A)) ↔
      IntegrableOn (fun u => (u/spectralWeylRadius A u) • F (spectralWeylRadius A u)) (Ioi (0 : ℝ)) := by
  rw [← spectralWeylRadius_image hA]
  rw [integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
    (fun u _ => (spectralWeylRadius_hasDerivAt hA u).hasDerivWithinAt)
    (spectralWeylRadius_injOn hA)]
  apply integrableOn_congr_fun
  · intro u hu
    dsimp only
    rw [abs_of_pos (div_pos hu (spectralWeylRadius_pos hA u))]
  · exact measurableSet_Ioi

end ArtinMatthews
