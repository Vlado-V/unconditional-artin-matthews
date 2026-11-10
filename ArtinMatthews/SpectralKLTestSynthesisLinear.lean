module

public import ArtinMatthews.SpectralKLTestSpace
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
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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

/-! The literal integral synthesis on the dense smooth test vector space,
as a linear map into the actual physical L2 space. -/

noncomputable section
open Set MeasureTheory Filter
open OAI.CubicEisenstein
open scoped Topology ContDiff

namespace ArtinMatthews

theorem spectralKLWeightedSynthesis_integrand_integrable (g : ℝ → ℂ) (hg : Continuous g)
    (hgc : HasCompactSupport g) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => schlafliBesselK ((t : ℂ)*Complex.I) x*g t*
      (spectralKLPlancherelWeight t : ℂ)) (Ioi (0 : ℝ)) := by
  let f : ℝ → ℂ := fun t => (spectralKLPlancherelWeight t : ℂ)*g t
  have hf : Continuous f := (Complex.continuous_ofReal.comp spectralKLPlancherelWeight_continuous).mul hg
  have hfc : HasCompactSupport f := hgc.mul_left
  apply (spectralKLSynthesis_integrand_integrable f hf hfc hx).restrict.congr
  filter_upwards with t
  rw [schlafliBesselK_imaginary_eq_realKernel t hx]
  dsimp [f]
  ring

theorem spectralKLWeightedSynthesis_add (f g : ℝ → ℂ) (hf : Continuous f) (hg : Continuous g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) {x : ℝ} (hx : 0 < x) :
    spectralKLWeightedSynthesis (f+g) x = spectralKLWeightedSynthesis f x+spectralKLWeightedSynthesis g x := by
  unfold spectralKLWeightedSynthesis
  simp_rw [Pi.add_apply,mul_add,add_mul]
  exact integral_add (spectralKLWeightedSynthesis_integrand_integrable f hf hfc hx)
    (spectralKLWeightedSynthesis_integrand_integrable g hg hgc hx)

theorem spectralKLWeightedSynthesis_smul (c : ℂ) (g : ℝ → ℂ) (x : ℝ) :
    spectralKLWeightedSynthesis (c • g) x = c • spectralKLWeightedSynthesis g x := by
  unfold spectralKLWeightedSynthesis
  rw [smul_eq_mul,← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  dsimp only [Pi.smul_apply,smul_eq_mul]
  ring

def spectralKLTestSynthesis (g : spectralKLTestSubmodule) : Lp ℂ 2 spectralKLPhysicalMeasure :=
  (spectralKLWeightedSynthesis_memLp g g.property.1.continuous g.property.2.1 g.property.2.2).toLp
    (spectralKLWeightedSynthesis g)

theorem spectralKLTestSynthesis_coe (g : spectralKLTestSubmodule) :
    spectralKLTestSynthesis g =ᵐ[spectralKLPhysicalMeasure] spectralKLWeightedSynthesis g :=
  MemLp.coeFn_toLp (spectralKLWeightedSynthesis_memLp g g.property.1.continuous g.property.2.1 g.property.2.2)

theorem spectralKLTestSynthesis_add (f g : spectralKLTestSubmodule) :
    spectralKLTestSynthesis (f+g) = spectralKLTestSynthesis f+spectralKLTestSynthesis g := by
  unfold spectralKLTestSynthesis
  rw [← MemLp.toLp_add]
  apply (MemLp.toLp_eq_toLp_iff _ _).mpr
  filter_upwards [spectralKLPositiveWeightMeasure_ae_pos (fun x => x⁻¹)] with x hx
  exact spectralKLWeightedSynthesis_add f g f.property.1.continuous g.property.1.continuous
    f.property.2.1 g.property.2.1 hx

theorem spectralKLTestSynthesis_smul (c : ℂ) (g : spectralKLTestSubmodule) :
    spectralKLTestSynthesis (c • g) = c • spectralKLTestSynthesis g := by
  unfold spectralKLTestSynthesis
  rw [← MemLp.toLp_const_smul]
  apply (MemLp.toLp_eq_toLp_iff _ _).mpr
  filter_upwards with x
  exact spectralKLWeightedSynthesis_smul c g x

def spectralKLTestSynthesisLinear : spectralKLTestSubmodule →ₗ[ℂ] Lp ℂ 2 spectralKLPhysicalMeasure where
  toFun := spectralKLTestSynthesis
  map_add' := spectralKLTestSynthesis_add
  map_smul' := spectralKLTestSynthesis_smul

theorem spectralKLTestSynthesis_norm (g : spectralKLTestSubmodule) :
    ‖spectralKLTestSynthesisLinear g‖ = ‖spectralKLTestToLp g‖ :=
  spectralKLWeightedSynthesis_toLp_norm g g.property.1.continuous g.property.2.1 g.property.2.2

end ArtinMatthews
