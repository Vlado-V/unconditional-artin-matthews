module

public import ArtinMatthews.SpectralGamma0EllipticMassCompletion
public import ArtinMatthews.SpectralGamma0EllipticHeightWeight
public import ArtinMatthews.SpectralGamma0WeakInverse
public import OAI.Analysis.PDE.Weak.Elliptic.Cutoff
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import OAI.Analysis.PDE.Weak.Elliptic.Coefficient


set_option backward.privateInPublic true
@[expose] public section

/-! A genuine native Euclidean L² forcing term for the actual Green vector.
Its source is the full automorphic L² datum, with no smoothness assumption.
The inverse-height cutoff agrees exactly with y⁻² on the local chart. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups
open OAI.Analysis.PDE.Weak OAI.Analysis.PDE.Variational

namespace ArtinMatthews

variable (φ : SchwartzMap (ℝ × ℝ) ℂ) {A a b : ℝ}
  (ha : 0 < a) (hab : a ≤ b) (hφ : tsupport φ ⊆ spectralPlaneRectangle A a b)
  (r : SL(2, ℤ)) (L : ℂ →L[ℝ] ℝ)

def gamma0EllipticForcing (N : ℕ) [NeZero N] (f : Gamma0RegionL2 N) :
    Lp ℝ 2 (volume : Measure (Fin 2 → ℝ)) :=
  cutoffL2 (spectralEllipticInverseHeight a) (spectralEllipticInverseHeight_continuous ha)
    (spectralEllipticInverseHeight_bound ha)
    (gamma0EllipticMass φ ha hφ r L N (f-gamma0Green N f))

theorem gamma0EllipticForcing_norm_le (N : ℕ) [NeZero N] (f : Gamma0RegionL2 N) :
    ‖gamma0EllipticForcing φ ha hφ r L N f‖ ≤
      (1/a^2)*‖gamma0EllipticMass φ ha hφ r L N (f-gamma0Green N f)‖ :=
  norm_cutoffL2_le _ _ _ _

include hab in
theorem gamma0EllipticForcing_ae (N : ℕ) [NeZero N] (f : Gamma0RegionL2 N) :
    ∀ᵐ x : Fin 2 → ℝ, a ≤ x 1 →
      gamma0EllipticForcing φ ha hφ r L N f x =
        (gamma0EllipticMass φ ha hφ r L N f x -
          (gamma0EllipticPair φ ha hφ r L N (gamma0WeakSolution N f)).1 x)/(x 1)^2 := by
  have he : gamma0EllipticMass φ ha hφ r L N (f-gamma0Green N f) =
      gamma0EllipticMass φ ha hφ r L N f -
        (gamma0EllipticPair φ ha hφ r L N (gamma0WeakSolution N f)).1 := by
    rw [map_sub,gamma0Green_apply,gamma0EllipticMass_energy φ ha hab hφ r L N]
  have hc := cutoffL2_ae (spectralEllipticInverseHeight a)
    (spectralEllipticInverseHeight_continuous ha) (spectralEllipticInverseHeight_bound ha)
    (gamma0EllipticMass φ ha hφ r L N (f-gamma0Green N f))
  change gamma0EllipticForcing φ ha hφ r L N f =ᵐ[volume] _ at hc
  rw [he] at hc
  filter_upwards [hc,Lp.coeFn_sub (gamma0EllipticMass φ ha hφ r L N f)
    (gamma0EllipticPair φ ha hφ r L N (gamma0WeakSolution N f)).1] with x hx hy
  intro hax
  rw [hx,hy,spectralEllipticInverseHeight_eq hax]
  simp only [Pi.sub_apply,smul_eq_mul]
  ring

end ArtinMatthews
