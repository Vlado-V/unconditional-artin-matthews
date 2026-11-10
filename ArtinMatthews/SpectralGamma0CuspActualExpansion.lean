module

public import ArtinMatthews.SpectralGamma0CuspActual
public import ArtinMatthews.SpectralGamma0SpectralCutoff
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


set_option backward.privateInPublic true
@[expose] public section

/-! Complete bounded-window spectral expansions in the actual cuspidal mass space.
Finite windows retain every multiplicity and exhaust the genuine Hilbert basis. -/
namespace ArtinMatthews
open Set Filter Topology
open scoped InnerProductSpace BigOperators
noncomputable section

local instance cuspActualExpansion_innerProduct (N : ℕ) [NeZero N] :
    InnerProductSpace ℂ (gamma0AllHeightCuspidalMassSpace N) :=
  Submodule.innerProductSpace (𝕜 := ℂ) (E := Gamma0RegionL2 N) (gamma0AllHeightCuspidalMassSpace N)

theorem gamma0AllHeightGradientSpectralCutoff_mono (N : ℕ) [NeZero N] :
    Monotone (gamma0AllHeightGradientSpectralCutoff N) := by
  intro R S hRS i hi
  exact (mem_gamma0AllHeightGradientSpectralCutoff N S i).mpr
    (((mem_gamma0AllHeightGradientSpectralCutoff N R i).mp hi).trans hRS)

theorem gamma0AllHeightGradientSpectralCutoff_tendsto (N : ℕ) [NeZero N] :
    Tendsto (gamma0AllHeightGradientSpectralCutoff N) atTop atTop := by
  classical
  refine tendsto_atTop_atTop.mpr ?_
  intro s
  refine ⟨∑ i ∈ s, gamma0AllHeightGradientSpectralValue N i, ?_⟩
  intro R hR i hi
  apply (mem_gamma0AllHeightGradientSpectralCutoff N R i).mpr
  exact (Finset.single_le_sum (fun j _ => gamma0AllHeightGradientSpectralValue_nonneg N j) hi).trans hR

theorem gamma0FullCuspidalSpectralBasis_hasSum (N : ℕ) [NeZero N]
    (f : gamma0AllHeightCuspidalMassSpace N) :
    HasSum (fun i : Gamma0AllHeightSpectralIndex N =>
      inner ℂ (gamma0FullCuspidalSpectralBasis N i) f • gamma0FullCuspidalSpectralBasis N i) f := by
  simpa only [HilbertBasis.repr_apply_apply] using (gamma0FullCuspidalSpectralBasis N).hasSum_repr f

theorem gamma0FullCuspidalSpectralBasis_cutoff_tendsto (N : ℕ) [NeZero N]
    (f : gamma0AllHeightCuspidalMassSpace N) :
    Tendsto (fun R : ℝ => ∑ i ∈ gamma0AllHeightGradientSpectralCutoff N R,
      inner ℂ (gamma0FullCuspidalSpectralBasis N i) f • gamma0FullCuspidalSpectralBasis N i)
      atTop (𝓝 f) :=
  (gamma0FullCuspidalSpectralBasis_hasSum N f).comp
    (gamma0AllHeightGradientSpectralCutoff_tendsto N)

theorem gamma0FullCuspidalSpectralBasis_ambient_cutoff_tendsto (N : ℕ) [NeZero N]
    (f : Gamma0RegionL2 N) (hf : f ∈ gamma0AllHeightCuspidalMassSpace N) :
    Tendsto (fun R : ℝ => ∑ i ∈ gamma0AllHeightGradientSpectralCutoff N R,
      inner ℂ (gamma0FullCuspidalSpectralBasis N i).val f •
        (gamma0FullCuspidalSpectralBasis N i).val) atTop (𝓝 f) := by
  have h := ((gamma0AllHeightCuspidalMassSpace N).subtypeL.continuous.tendsto ⟨f, hf⟩).comp
    (gamma0FullCuspidalSpectralBasis_cutoff_tendsto N ⟨f, hf⟩)
  simpa only [Function.comp_def, ContinuousLinearMap.coe_coe, map_sum, map_smul,
    Submodule.subtypeL_apply, Submodule.coe_inner] using h

end
end ArtinMatthews
