module

public import ArtinMatthews.SpectralEisensteinChannelSurjectivity
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

/-! The normalized Eisenstein channel space is unitarily equivalent to
the actual ambient sector orthogonal to the cusp and residual spectra. -/
noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace
namespace ArtinMatthews

abbrev Gamma0ContinuousSpectralMassSpace (N : ℕ) [NeZero N] : Submodule ℂ (Gamma0RegionL2 N) :=
  (gamma0AllHeightCuspidalMassSpace N)ᗮ ⊓ (gamma0ResidualProjection N).ker

theorem gamma0EisensteinSynthesis_mem_continuous (N : ℕ) [NeZero N]
    (v : Gamma0EisensteinSpectralSpace N) :
    (gamma0EisensteinAnalysis N).adjoint v∈Gamma0ContinuousSpectralMassSpace N := by
  constructor
  · intro u hu
    rw [ContinuousLinearMap.adjoint_inner_right,gamma0EisensteinAnalysis_cuspidal_zero N ⟨u,hu⟩,
      inner_zero_left]
  · exact gamma0EisensteinSynthesis_residual_projection_zero N v

theorem gamma0ContinuousSpectralMass_resolution (N : ℕ) [NeZero N]
    (f : Gamma0ContinuousSpectralMassSpace N) :
    (gamma0EisensteinAnalysis N).adjoint (gamma0EisensteinAnalysis N f.val)=f.val := by
  have h := gamma0AmbientEisenstein_resolution N f.val
  have hp : gamma0CuspidalProjection N f.val=0 :=
    Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr f.property.1
  have hr : gamma0ResidualProjection N f.val=0 := f.property.2
  rw [hp,Submodule.coe_zero,hr,zero_add,zero_add] at h
  exact h.symm

def gamma0EisensteinContinuousSynthesis (N : ℕ) [NeZero N] :
    Gamma0EisensteinSpectralSpace N →ₗᵢ[ℂ] Gamma0ContinuousSpectralMassSpace N where
  toFun v := ⟨(gamma0EisensteinAnalysis N).adjoint v,gamma0EisensteinSynthesis_mem_continuous N v⟩
  map_add' v w := Subtype.ext (map_add (gamma0EisensteinAnalysis N).adjoint v w)
  map_smul' c v := Subtype.ext (map_smul (gamma0EisensteinAnalysis N).adjoint c v)
  norm_map' := gamma0EisensteinSynthesis_norm N

theorem gamma0EisensteinContinuousSynthesis_surjective (N : ℕ) [NeZero N] :
    Function.Surjective (gamma0EisensteinContinuousSynthesis N) := by
  intro f
  refine ⟨gamma0EisensteinAnalysis N f.val,?_⟩
  exact Subtype.ext (gamma0ContinuousSpectralMass_resolution N f)

def gamma0EisensteinContinuousUnitary (N : ℕ) [NeZero N] :
    Gamma0EisensteinSpectralSpace N ≃ₗᵢ[ℂ] Gamma0ContinuousSpectralMassSpace N :=
  LinearIsometryEquiv.ofSurjective (gamma0EisensteinContinuousSynthesis N)
    (gamma0EisensteinContinuousSynthesis_surjective N)

theorem gamma0EisensteinContinuousUnitary_apply (N : ℕ) [NeZero N]
    (v : Gamma0EisensteinSpectralSpace N) :
    (gamma0EisensteinContinuousUnitary N v).val=(gamma0EisensteinAnalysis N).adjoint v := rfl

theorem gamma0EisensteinContinuousUnitary_symm (N : ℕ) [NeZero N]
    (f : Gamma0ContinuousSpectralMassSpace N) :
    (gamma0EisensteinContinuousUnitary N).symm f=gamma0EisensteinAnalysis N f.val := by
  apply (gamma0EisensteinContinuousUnitary N).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact (Subtype.ext (gamma0ContinuousSpectralMass_resolution N f)).symm

end ArtinMatthews
