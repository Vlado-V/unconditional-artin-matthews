module

public import ArtinMatthews.SpectralWeylRadiusSubstitution
public import ArtinMatthews.SpectralGaussianCosine
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Actual Gaussian evaluation of the supported radial cosine kernel.
This removes the square-root boundary singularity with its full Jacobian. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace ArtinMatthews

def spectralWeylRadialKernel (A b X : ℝ) : ℝ :=
  if Real.sqrt A < X then
    2*Real.cos (b*Real.sqrt (X^2-A))/Real.sqrt (X^2-A) else 0

def spectralWeylRadialGaussian (A b p X : ℝ) : ℝ :=
  Real.exp (-p*X^2)*X*spectralWeylRadialKernel A b X

theorem spectralWeylRadialGaussian_support (A b p : ℝ) :
    Function.support (spectralWeylRadialGaussian A b p) ⊆ Ioi (Real.sqrt A) := by
  intro X hX
  by_contra h
  change ¬Real.sqrt A < X at h
  exact hX (by simp [spectralWeylRadialGaussian,spectralWeylRadialKernel,h])

theorem spectralWeylRadialGaussian_substitution {A : ℝ} (hA : 0 < A) (b p : ℝ)
    {u : ℝ} (hu : 0 < u) :
    (u/spectralWeylRadius A u)*spectralWeylRadialGaussian A b p (spectralWeylRadius A u) =
      (2*Real.exp (-p*A))*(Real.exp (-p*u^2)*Real.cos (b*u)) := by
  have hR : Real.sqrt A < spectralWeylRadius A u := by
    have hmem : spectralWeylRadius A u ∈ spectralWeylRadius A '' Ioi (0 : ℝ) := ⟨u,hu,rfl⟩
    rwa [spectralWeylRadius_image hA] at hmem
  have hs : Real.sqrt ((spectralWeylRadius A u)^2-A) = u := by
    rw [spectralWeylRadius_sq hA,add_sub_cancel_left,Real.sqrt_sq hu.le]
  unfold spectralWeylRadialGaussian spectralWeylRadialKernel
  rw [ite_eq_left hR,hs,spectralWeylRadius_sq hA]
  rw [show -p*(A+u^2) = -p*A+-p*u^2 by ring,Real.exp_add]
  field_simp [(spectralWeylRadius_pos hA u).ne',hu.ne']

theorem spectralWeylRadialGaussian_integrable {A p : ℝ} (hA : 0 < A) (hp : 0 < p) (b : ℝ) :
    Integrable (spectralWeylRadialGaussian A b p) := by
  apply (integrableOn_iff_integrable_of_support_subset (spectralWeylRadialGaussian_support A b p)).mp
  apply (spectralWeylRadius_integrable hA _).mpr
  apply ((spectralGaussianCosine_integrable hp b).const_mul (2*Real.exp (-p*A))).restrict.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact (spectralWeylRadialGaussian_substitution hA b p hu).symm

theorem spectralWeylRadialGaussian_integral {A p : ℝ} (hA : 0 < A) (hp : 0 < p) (b : ℝ) :
    (∫ X in Ioi (0 : ℝ), spectralWeylRadialGaussian A b p X) =
      Real.sqrt (Real.pi/p)*Real.exp (-p*A-b^2/(4*p)) := by
  have hzero (X : ℝ) (hX : X ∉ Ioi (Real.sqrt A)) :
      spectralWeylRadialGaussian A b p X = 0 := by
    change ¬Real.sqrt A < X at hX
    simp [spectralWeylRadialGaussian,spectralWeylRadialKernel,hX]
  have hzero0 (X : ℝ) (hX : X ∉ Ioi (0 : ℝ)) :
      spectralWeylRadialGaussian A b p X = 0 := by
    apply hzero
    intro h
    exact hX ((Real.sqrt_nonneg A).trans_lt h)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero0,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero hzero,spectralWeylRadius_integral hA]
  calc
    _ = (2*Real.exp (-p*A))*(∫ u in Ioi (0 : ℝ), Real.exp (-p*u^2)*Real.cos (b*u)) := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      exact spectralWeylRadialGaussian_substitution hA b p hu
    _ = Real.exp (-p*A)*((2 : ℝ)*(∫ u in Ioi (0 : ℝ), Real.exp (-p*u^2)*Real.cos (b*u))) := by ring
    _ = _ := by
      rw [spectralGaussianCosine_Ioi hp b,show -p*A-b^2/(4*p) = -p*A+(-(b^2)/(4*p)) by ring,Real.exp_add]
      ring

end ArtinMatthews
