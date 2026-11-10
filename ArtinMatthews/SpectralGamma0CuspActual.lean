module

public import ArtinMatthews.SpectralGamma0GreenCuspInvariant
public import ArtinMatthews.SpectralGamma0CuspEigenfunctionsCompatibility
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

/-! Unconditional spectral data on the genuine all-height cuspidal mass kernel.
The analytic Green-preservation theorem discharges the explicit hypothesis in
previous structural compatibility lemmas. Coordinate smoothness is a separate
elliptic regularity result. -/
namespace ArtinMatthews
open Set Topology
open scoped InnerProductSpace MatrixGroups
noncomputable section

local instance cuspActual_trueInnerProduct (N : ℕ) [NeZero N] :
    InnerProductSpace ℂ (gamma0AllHeightCuspidalMassSpace N) :=
  Submodule.innerProductSpace (𝕜 := ℂ) (E := Gamma0RegionL2 N) (gamma0AllHeightCuspidalMassSpace N)
local instance cuspActual_energyInner (N : ℕ) [NeZero N] :
    Inner ℂ (gamma0AllHeightMeanZeroEnergy N) :=
  (gamma0AllHeightMeanZeroEnergy_innerProductSpace N).toInner
local instance cuspActual_massInner (N : ℕ) [NeZero N] :
    Inner ℂ (gamma0AllHeightEnergyMassSpace N) :=
  (gamma0AllHeightEnergyMassSpace_innerProductSpace N).toInner

theorem gamma0AllHeight_mass_closure_eq (N : ℕ) [NeZero N] :
    gamma0AllHeightEnergyMassSpace N = gamma0AllHeightCuspidalMassSpace N :=
  gamma0AllHeight_mass_closure_eq_of_green_invariant N
    (gamma0Green_mem_allHeightCuspidalMassSpace N)

theorem gamma0WeakSolution_mem_allHeight (N : ℕ) [NeZero N]
    (f : Gamma0RegionL2 N) (hf : f ∈ gamma0AllHeightCuspidalMassSpace N) :
    gamma0WeakSolution N f ∈ gamma0AllHeightMeanZeroEnergy N :=
  gamma0WeakSolution_mem_allHeight_of_green_invariant N
    (gamma0Green_mem_allHeightCuspidalMassSpace N) f hf

def gamma0CuspidalGreen (N : ℕ) [NeZero N] :
    gamma0AllHeightCuspidalMassSpace N →L[ℂ] gamma0AllHeightCuspidalMassSpace N :=
  gamma0CuspidalGreenOfInvariant N (gamma0Green_mem_allHeightCuspidalMassSpace N)

theorem gamma0CuspidalGreen_apply (N : ℕ) [NeZero N]
    (f : gamma0AllHeightCuspidalMassSpace N) :
    (gamma0CuspidalGreen N f).val = gamma0Green N f.val := rfl

theorem gamma0CuspidalGreen_selfAdjoint (N : ℕ) [NeZero N] :
    IsSelfAdjoint (gamma0CuspidalGreen N) :=
  gamma0CuspidalGreenOfInvariant_selfAdjoint N (gamma0Green_mem_allHeightCuspidalMassSpace N)

theorem gamma0CuspidalGreen_compact (N : ℕ) [NeZero N] :
    IsCompactOperator (gamma0CuspidalGreen N) :=
  gamma0CuspidalGreenOfInvariant_compact N (gamma0Green_mem_allHeightCuspidalMassSpace N)

theorem gamma0CuspidalGreen_injective (N : ℕ) [NeZero N] :
    Function.Injective (gamma0CuspidalGreen N) :=
  gamma0CuspidalGreenOfInvariant_injective N (gamma0Green_mem_allHeightCuspidalMassSpace N)

theorem gamma0CuspidalGreen_denseRange (N : ℕ) [NeZero N] :
    DenseRange (gamma0CuspidalGreen N) :=
  gamma0CuspidalGreenOfInvariant_denseRange N (gamma0Green_mem_allHeightCuspidalMassSpace N)

def gamma0FullCuspidalSpectralBasis (N : ℕ) [NeZero N] :
    HilbertBasis (Gamma0AllHeightSpectralIndex N) ℂ (gamma0AllHeightCuspidalMassSpace N) :=
  gamma0FullCuspidalSpectralBasisOfInvariant N (gamma0Green_mem_allHeightCuspidalMassSpace N)

theorem gamma0FullCuspidalSpectralBasis_coe (N : ℕ) [NeZero N]
    (i : Gamma0AllHeightSpectralIndex N) :
    (gamma0FullCuspidalSpectralBasis N i).val = (gamma0AllHeightSpectralBasis N i).val := rfl

theorem gamma0FullCuspidalSpectralBasis_eigen (N : ℕ) [NeZero N]
    (i : Gamma0AllHeightSpectralIndex N) :
    gamma0Green N (gamma0FullCuspidalSpectralBasis N i).val =
      i.1 • (gamma0FullCuspidalSpectralBasis N i).val :=
  gamma0FullCuspidalSpectralBasisOfInvariant_eigen N
    (gamma0Green_mem_allHeightCuspidalMassSpace N) i

theorem gamma0AllHeightSpectralEnergy_ambient_weak (N : ℕ) [NeZero N]
    (i : Gamma0AllHeightSpectralIndex N) (v : gamma0EnergySpace N) :
    inner ℂ (gamma0AllHeightSpectralEnergy N i).val v =
      (i.1.re⁻¹ : ℂ) * inner ℂ (gamma0FullCuspidalSpectralBasis N i).val
        (gamma0EnergyInclusion N v) :=
  gamma0AllHeightSpectralEnergy_ambient_weak_of_green_invariant N
    (gamma0Green_mem_allHeightCuspidalMassSpace N) i v

theorem gamma0AllHeightSpectralEnergy_ambient_gradient (N : ℕ) [NeZero N]
    (i : Gamma0AllHeightSpectralIndex N) (v : gamma0EnergySpace N) :
    inner ℂ (gamma0EnergyGradient N (gamma0AllHeightSpectralEnergy N i).val)
      (gamma0EnergyGradient N v) =
        (gamma0AllHeightGradientSpectralValue N i : ℂ) *
          inner ℂ (gamma0FullCuspidalSpectralBasis N i).val (gamma0EnergyInclusion N v) :=
  gamma0AllHeightSpectralEnergy_ambient_gradient_of_green_invariant N
    (gamma0Green_mem_allHeightCuspidalMassSpace N) i v

end
end ArtinMatthews
