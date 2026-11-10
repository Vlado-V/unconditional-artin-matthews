module

public import ArtinMatthews.SpectralGamma0CompactInclusion
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

/-! The actual mass closure of the all-positive-height mean-zero energy
space, and its compact dense form inclusion. This is an honest closure
construction; identification with a separately defined full cuspidal L²
space is a further theorem. -/
noncomputable section
open Set Topology
namespace ArtinMatthews

instance gamma0AllHeightMeanZeroEnergy_innerProductSpace (N : ℕ) [NeZero N] :
    InnerProductSpace ℂ (gamma0AllHeightMeanZeroEnergy N) :=
  Submodule.innerProductSpace (𝕜 := ℂ) (E := gamma0EnergySpace N) (gamma0AllHeightMeanZeroEnergy N)

def gamma0AllHeightEnergyMassSpace (N : ℕ) [NeZero N] : Submodule ℂ (Gamma0RegionL2 N) :=
  (gamma0AllHeightMassInclusion N).range.topologicalClosure

instance gamma0AllHeightEnergyMassSpace_innerProductSpace (N : ℕ) [NeZero N] :
    InnerProductSpace ℂ (gamma0AllHeightEnergyMassSpace N) :=
  Submodule.innerProductSpace (𝕜 := ℂ) (E := Gamma0RegionL2 N) (gamma0AllHeightEnergyMassSpace N)

instance gamma0AllHeightEnergyMassSpace_complete (N : ℕ) [NeZero N] :
    CompleteSpace (gamma0AllHeightEnergyMassSpace N) :=
  (Submodule.isClosed_topologicalClosure _).isComplete.completeSpace_coe

def gamma0AllHeightCoreInclusion (N : ℕ) [NeZero N] :
    gamma0AllHeightMeanZeroEnergy N →L[ℂ] gamma0AllHeightEnergyMassSpace N :=
  (gamma0AllHeightMassInclusion N).codRestrict (gamma0AllHeightEnergyMassSpace N)
    (fun u => Submodule.le_topologicalClosure _ ⟨u,rfl⟩)

theorem gamma0AllHeightCoreInclusion_coe (N : ℕ) [NeZero N]
    (u : gamma0AllHeightMeanZeroEnergy N) :
    (gamma0AllHeightCoreInclusion N u).val = gamma0EnergyInclusion N u.val := rfl

theorem gamma0AllHeightCoreInclusion_bound (N : ℕ) [NeZero N]
    (u : gamma0AllHeightMeanZeroEnergy N) : ‖gamma0AllHeightCoreInclusion N u‖ ≤ ‖u‖ :=
  gamma0EnergyInclusion_bound N u.val

theorem gamma0AllHeightCoreInclusion_denseRange (N : ℕ) [NeZero N] :
    DenseRange (gamma0AllHeightCoreInclusion N) := by
  intro u
  rw [IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
  have he : Subtype.val '' range (gamma0AllHeightCoreInclusion N) =
      range (gamma0AllHeightMassInclusion N) := by
    ext y
    constructor
    · rintro ⟨v, ⟨w,rfl⟩,rfl⟩
      exact ⟨w,rfl⟩
    · rintro ⟨w,rfl⟩
      exact ⟨gamma0AllHeightCoreInclusion N w, ⟨w,rfl⟩,rfl⟩
  rw [he]
  exact u.property

theorem gamma0AllHeightCoreInclusion_compact (N : ℕ) [NeZero N] :
    IsCompactOperator (gamma0AllHeightCoreInclusion N) :=
  (gamma0AllHeightMassInclusion_compact N).codRestrict
    (V := gamma0AllHeightEnergyMassSpace N)
    (fun u => Submodule.le_topologicalClosure (gamma0AllHeightMassInclusion N).range ⟨u,rfl⟩)
    (Submodule.isClosed_topologicalClosure _)

end ArtinMatthews
