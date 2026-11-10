module

public import ArtinMatthews.SpectralRellichRectangle
public import ArtinMatthews.SpectralHyperbolicGreen
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! The proved Rellich energy is the actual Schwartz Dirichlet form. -/
namespace ArtinMatthews

open MeasureTheory Set
open scoped SchwartzMap LineDeriv

theorem spectralPlanePartialX_schwartz (F : SchwartzMap (ℝ × ℝ) ℂ) (p : ℝ × ℝ) :
    spectralPlanePartialX F p = (∂_{((1,0) : ℝ × ℝ)} F) p := by
  rw [spectralPlanePartialX_eq_fderiv F.differentiableAt,SchwartzMap.lineDerivOp_apply_eq_fderiv]

theorem spectralPlanePartialY_schwartz (F : SchwartzMap (ℝ × ℝ) ℂ) (p : ℝ × ℝ) :
    spectralPlanePartialY F p = (∂_{((0,1) : ℝ × ℝ)} F) p := by
  rw [spectralPlanePartialY_eq_fderiv F.differentiableAt,SchwartzMap.lineDerivOp_apply_eq_fderiv]

/-- Equality with the actual Dirichlet density in the hyperbolic Green identity. -/
theorem spectralPlaneH1Energy_eq_dirichlet (F : SchwartzMap (ℝ × ℝ) ℂ) :
    spectralPlaneH1Energy F = (∫ p, ‖F p‖^2)+∫ p, h2DirichletDensity F F p := by
  unfold spectralPlaneH1Energy h2DirichletDensity
  simp_rw [spectralPlanePartialX_schwartz,spectralPlanePartialY_schwartz,real_inner_self_eq_norm_sq]

/-- Compactness of the actual supported rectangle family with its actual
Schwartz Dirichlet energy, ready for finite hyperbolic chart assembly. -/
theorem spectral_rellich_rectangle_dirichlet {J : Type*} (A a b : ℝ)
    (F : J → SchwartzMap (ℝ × ℝ) ℂ)
    (hs : ∀ j, tsupport (F j) ⊆ spectralPlaneRectangle A a b) {B : ℝ} (hB : 0 ≤ B)
    (henergy : ∀ j, (∫ p, ‖F j p‖^2)+∫ p, h2DirichletDensity (F j) (F j) p ≤ B) :
    let hc : ∀ j, HasCompactSupport (F j) := fun j => (spectralPlaneRectangle_compact A a b).of_isClosed_subset
      (isClosed_tsupport _) (hs j)
    IsCompact (closure (range (fun j => spectralPlaneLp (F j) (F j).continuous (hc j)))) := by
  apply spectral_rellich_rectangle A a b F hs hB
  intro j
  rw [spectralPlaneH1Energy_eq_dirichlet]
  exact henergy j

end ArtinMatthews
