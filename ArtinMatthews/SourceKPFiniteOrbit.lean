module

public import ArtinMatthews.SourceKPArchComponent
public import ArtinMatthews.SourceKPFiniteLevelTopology
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

namespace ArtinMatthews
open NumberField Matrix Topology
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def SourceKPFiniteOrbit :=
  Quotient (MulAction.orbitRel (PGL(2, K)) (SourceKPFiniteLevelFiber K hζ))

instance sourceKPFiniteOrbit_topology : TopologicalSpace (SourceKPFiniteOrbit K hζ) := ⊥
instance sourceKPFiniteOrbit_discrete : DiscreteTopology (SourceKPFiniteOrbit K hζ) := ⟨rfl⟩

def sourceKPFiniteOrbitMk (b : SourceKPFiniteLevelFiber K hζ) : SourceKPFiniteOrbit K hζ :=
  Quotient.mk _ b

def sourceKPAutomorphicFiniteOrbit : SourceKPAutomorphicLevel K hζ → SourceKPFiniteOrbit K hζ :=
  Quotient.lift (fun x : SourceKPFiniteLevelSpace K hζ => sourceKPFiniteOrbitMk K hζ x.2) (by
    intro x y hxy
    obtain ⟨γ,hγ⟩ := MulAction.mem_orbit_iff.mp hxy
    apply Quotient.sound
    apply MulAction.mem_orbit_iff.mpr
    exact ⟨γ,congrArg (fun x : SourceKPFiniteLevelSpace K hζ => x.2) hγ⟩)

theorem sourceKPAutomorphicFiniteOrbit_component (b : SourceKPFiniteLevelFiber K hζ)
    (a : PGL(2, InfiniteAdeleRing K)) :
    sourceKPAutomorphicFiniteOrbit K hζ (sourceKPArchComponentPoint K hζ b a) =
      sourceKPFiniteOrbitMk K hζ b := rfl

theorem sourceKPAutomorphicFiniteOrbit_continuous : Continuous (sourceKPAutomorphicFiniteOrbit K hζ) :=
  ((continuous_of_discreteTopology : Continuous (sourceKPFiniteOrbitMk K hζ)).comp
    continuous_snd).quotient_lift _

theorem sourceKPArchComponentPoint_continuous (b : SourceKPFiniteLevelFiber K hζ) :
    Continuous (sourceKPArchComponentPoint K hζ b) :=
  continuous_quot_mk.comp (continuous_id.prodMk continuous_const)

theorem sourceKPArchComponentEmbedding_continuous (b : SourceKPFiniteLevelFiber K hζ) :
    Continuous (sourceKPArchComponentEmbedding K hζ b) :=
  (sourceKPArchComponentPoint_continuous K hζ b).quotient_lift _

theorem sourceKPArchComponent_range (b : SourceKPFiniteLevelFiber K hζ) :
    Set.range (sourceKPArchComponentPoint K hζ b) =
      (sourceKPAutomorphicFiniteOrbit K hζ) ⁻¹' {sourceKPFiniteOrbitMk K hζ b} := by
  ext x
  constructor
  · rintro ⟨a,rfl⟩
    rfl
  · intro hx
    induction x using Quotient.inductionOn with
    | _ x =>
      obtain ⟨a,c⟩ := x
      change sourceKPFiniteOrbitMk K hζ c = sourceKPFiniteOrbitMk K hζ b at hx
      obtain ⟨γ,hγ⟩ := MulAction.mem_orbit_iff.mp (Quotient.exact hx)
      refine ⟨(sourceKPRationalArchMap K hζ γ)⁻¹ * a,?_⟩
      apply Eq.symm
      apply Quotient.sound
      apply MulAction.mem_orbit_iff.mpr
      refine ⟨γ,Prod.ext ?_ hγ⟩
      change sourceKPRationalArchMap K hζ γ * ((sourceKPRationalArchMap K hζ γ)⁻¹ * a) = a
      exact mul_inv_cancel_left _ _

theorem sourceKPArchComponent_range_clopen (b : SourceKPFiniteLevelFiber K hζ) :
    IsClopen (Set.range (sourceKPArchComponentPoint K hζ b)) := by
  rw [sourceKPArchComponent_range]
  exact (isClopen_discrete _).preimage (sourceKPAutomorphicFiniteOrbit_continuous K hζ)

end
end ArtinMatthews
