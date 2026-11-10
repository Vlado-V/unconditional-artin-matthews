module

public import ArtinMatthews.SpectralEisensteinCriticalPoleRemoval
public import ArtinMatthews.SpectralEisensteinCriticalNorm
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
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
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

/-! The canonical scattering matrix is unitary at every critical parameter,
including the threshold and removable matching singularities. -/
noncomputable section
open Set Filter Topology Matrix
namespace ArtinMatthews

theorem gamma0CuspScatteringCanonical_mulVec_critical_continuous (N : ℕ) [NeZero N]
    (c : Gamma0EisensteinCuspClasses N → ℂ) (i : Gamma0EisensteinCuspClasses N) :
    Continuous (fun t : ℝ => (gamma0CuspScatteringCanonical N (eisensteinCriticalPoint t)).mulVec c i) := by
  change Continuous (fun t : ℝ => ∑ j, gamma0CuspScatteringCanonical N (eisensteinCriticalPoint t) i j*c j)
  refine continuous_finsetSum _ fun j _ => Continuous.mul ?_ continuous_const
  exact continuous_iff_continuousAt.mpr fun t =>
    (gamma0CuspScatteringCanonical_entry_analyticAt_critical N t i j).continuousAt.comp
      eisensteinCriticalPoint_continuous.continuousAt

theorem gamma0CuspScatteringCanonical_norm_sq_critical (N : ℕ) [NeZero N] (t : ℝ)
    (c : Gamma0EisensteinCuspClasses N → ℂ) :
    (∑ i,‖(gamma0CuspScatteringCanonical N (eisensteinCriticalPoint t)).mulVec c i‖^2)=
      ∑ i,‖c i‖^2 := by
  let f (u : ℝ) := ∑ i,‖(gamma0CuspScatteringCanonical N (eisensteinCriticalPoint u)).mulVec c i‖^2
  have hf : Continuous f :=
    continuous_finsetSum _ fun i _ => (gamma0CuspScatteringCanonical_mulVec_critical_continuous N c i).norm.pow 2
  have he : f =ᶠ[𝓝[≠] t] fun _ => ∑ i,‖c i‖^2 := by
    filter_upwards [gamma0EisensteinMatchingRegular_critical_eventually N t] with u hu
    change (∑ i,‖(gamma0CuspScatteringCanonical N (eisensteinCriticalPoint u)).mulVec c i‖^2)=_
    rw [gamma0CuspScatteringCanonical_eq_regular N _ hu.1]
    exact gamma0CuspScatteringMatrix_norm_sq_regular N _ (eisensteinCriticalPoint_re u)
      (by simpa only [eisensteinCriticalPoint_im] using hu.2) hu.1 c
  exact tendsto_nhds_unique (hf.continuousAt.mono_left nhdsWithin_le_nhds)
    (tendsto_const_nhds.congr' he.symm)

def gamma0CuspScatteringCriticalLinear (N : ℕ) [NeZero N] (t : ℝ) :
    EuclideanSpace ℂ (Gamma0EisensteinCuspClasses N) →ₗ[ℂ]
      EuclideanSpace ℂ (Gamma0EisensteinCuspClasses N) :=
  let e := WithLp.linearEquiv 2 ℂ (Gamma0EisensteinCuspClasses N → ℂ)
  e.symm.toLinearMap.comp ((gamma0CuspScatteringCanonical N (eisensteinCriticalPoint t)).mulVecLin.comp e.toLinearMap)

theorem gamma0CuspScatteringCriticalLinear_apply (N : ℕ) [NeZero N] (t : ℝ)
    (u : EuclideanSpace ℂ (Gamma0EisensteinCuspClasses N)) (i : Gamma0EisensteinCuspClasses N) :
    (gamma0CuspScatteringCriticalLinear N t u) i=
      (gamma0CuspScatteringCanonical N (eisensteinCriticalPoint t)).mulVec (fun j => u j) i := rfl

theorem gamma0CuspScatteringCriticalLinear_norm (N : ℕ) [NeZero N] (t : ℝ)
    (u : EuclideanSpace ℂ (Gamma0EisensteinCuspClasses N)) :
    ‖gamma0CuspScatteringCriticalLinear N t u‖=‖u‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2]
  simp only [gamma0CuspScatteringCriticalLinear_apply]
  exact gamma0CuspScatteringCanonical_norm_sq_critical N t (fun j => u j)

def gamma0CuspScatteringCriticalIsometry (N : ℕ) [NeZero N] (t : ℝ) :
    EuclideanSpace ℂ (Gamma0EisensteinCuspClasses N) →ₗᵢ[ℂ]
      EuclideanSpace ℂ (Gamma0EisensteinCuspClasses N) :=
  ⟨gamma0CuspScatteringCriticalLinear N t,gamma0CuspScatteringCriticalLinear_norm N t⟩

def gamma0CuspScatteringCriticalUnitary (N : ℕ) [NeZero N] (t : ℝ) :
    EuclideanSpace ℂ (Gamma0EisensteinCuspClasses N) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (Gamma0EisensteinCuspClasses N) :=
  LinearIsometryEquiv.ofSurjective (gamma0CuspScatteringCriticalIsometry N t)
    (LinearMap.surjective_of_injective (f:=gamma0CuspScatteringCriticalLinear N t)
      (gamma0CuspScatteringCriticalIsometry N t).injective)

theorem gamma0CuspScatteringCriticalUnitary_apply (N : ℕ) [NeZero N] (t : ℝ)
    (u : EuclideanSpace ℂ (Gamma0EisensteinCuspClasses N)) (i : Gamma0EisensteinCuspClasses N) :
    (gamma0CuspScatteringCriticalUnitary N t u) i=
      (gamma0CuspScatteringCanonical N (eisensteinCriticalPoint t)).mulVec (fun j => u j) i := rfl

end ArtinMatthews
