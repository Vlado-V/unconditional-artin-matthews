module

public import ArtinMatthews.SLocalNormOneGroup
public import ArtinMatthews.SLocalSUnitIsolation
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import Mathlib.Topology.Algebra.ProperAction.Basic
public import Mathlib.Topology.Connected.Separation
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The subgroup being divided out in the actual source integral is
discrete, closed, and countable. The literal quotient is compact and
Hausdorff; no separation premise on it is supplied. -/
namespace ArtinMatthews.SourcePhysical

open NumberField IsDedekindDomain
open scoped NumberField Classical
noncomputable section
variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))

theorem sNormOneSixthSubgroup_discrete : DiscreteTopology (sNormOneSixthSubgroup K S) := by
  rw [discreteTopology_iff_isOpen_singleton_one]
  obtain ⟨V, hV, h1, hIso⟩ := exists_sWholeUnit_open_isolation K S
  let f : sNormOneSixthSubgroup K S → SWholeUnits K S := fun x => x.val.val
  have hf : Continuous f := continuous_subtype_val.comp continuous_subtype_val
  have he : f ⁻¹' V = {1} := by
    ext x
    constructor
    · intro hx
      change x.val.val ∈ V at hx
      have hx' : ∃ u : SUnitGroup (K := K) S, sNormOneSixthMap K S u = x.val := x.property
      obtain ⟨u, hu⟩ := hx'
      have hd : sWholeDiagonal K S ((u ^ 6 : SUnitGroup (K := K) S) : Kˣ) = x.val.val :=
        congrArg Subtype.val hu
      apply Set.mem_singleton_iff.mpr
      apply Subtype.ext
      apply Subtype.ext
      exact hd.symm.trans (hIso (u ^ 6) (by rwa [hd]))
    · intro hx
      obtain rfl := Set.mem_singleton_iff.mp hx
      exact h1
  rw [← he]
  exact hV.preimage hf

theorem sNormOneSixthSubgroup_isClosed :
    IsClosed (sNormOneSixthSubgroup K S : Set (SNormOne K S)) := by
  let : DiscreteTopology (sNormOneSixthSubgroup K S) := sNormOneSixthSubgroup_discrete K S
  exact Subgroup.isClosed_of_discreteTopology

theorem sNormOneSixthQuotient_t2 : T2Space (SNormOneSixthQuotient K S) := by
  let : IsClosed (sNormOneSixthSubgroup K S : Set (SNormOne K S)) :=
    sNormOneSixthSubgroup_isClosed K S
  infer_instance

theorem sNormOneSixthSubgroup_countable : Countable (sNormOneSixthSubgroup K S) := by
  let : Countable K := (Module.finBasis ℚ K).repr.injective.countable
  let : Countable Kˣ := Units.val_injective.countable
  let f (u : SUnitGroup (K := K) S) : sNormOneSixthSubgroup K S :=
    ⟨sNormOneSixthMap K S u, ⟨u, rfl⟩⟩
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨u, hu⟩ := x.property
    exact ⟨u, Subtype.ext hu⟩
  exact hf.countable

end
end ArtinMatthews.SourcePhysical
