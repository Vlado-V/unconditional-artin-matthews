module

public import ArtinMatthews.SourceKPAdelicOutgoingLocalStableJacquet
public import ArtinMatthews.SourceRetainedGeneratorBasis
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
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
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

/-! A retained-place basis is chosen from the actual Jacquet values
of local translates of the exceptional outgoing vector. Its labels
and representatives depend on the retained places alone. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain
open scoped Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K)) (hs : 0 < (1 / 6 : ℂ).re)

local notation "s₀" => (1 / 6 : ℂ)
local notation "S₀" => (Singleton.singleton P : Finset (HeightOneSpectrum (𝓞 K)))
local notation "G₀" => SourceFiniteKP2Projective K hζ P
local notation "W" => sourceKPAdelicOutgoingRegularizedRetainedCarrier K hζ S₀ s₀ hs
local notation "ρ₀" => sourceKPAdelicOutgoingRegularizedLocalBorelRepresentation K hζ P s₀ hs
local notation "C" => sourceKPAdelicOutgoingRegularizedLocalCyclic K hζ P s₀ hs
local notation "hC" => sourceKPAdelicOutgoingRegularizedLocalCyclic_invariant K hζ P s₀ hs
local notation "v₀" => sourceKPAdelicOutgoingRegularizedLocalCyclicVector K hζ P s₀ hs
local notation "J" => sourceKPAdelicOutgoingRegularizedLocalJacquetMap K hζ P s₀ hs
local notation "π" => sourceKPJacquetRight K hζ P ρ₀ C hC

local instance sourceKPAdelicOutgoingRetainedJacquetBasisAddCommGroup : AddCommGroup W :=
  Submodule.addCommGroup _

local instance sourceKPAdelicOutgoingRetainedJacquetBasisFiniteDimensional : FiniteDimensional ℂ W :=
  sourceKPAdelicOutgoingRegularizedLocalCarrier_finiteDimensional K hζ P s₀ hs

def sourceKPAdelicOutgoingRetainedJacquetVector (a : G₀) : W := J (π a v₀)

local notation "v" => sourceKPAdelicOutgoingRetainedJacquetVector K hζ P hs

abbrev SourceKPAdelicOutgoingRetainedJacquetBasisIndex :=
  Fin (Module.finrank ℂ (Submodule.span ℂ (Set.range v)))

local notation "Index" => SourceKPAdelicOutgoingRetainedJacquetBasisIndex K hζ P hs

def sourceKPAdelicOutgoingRetainedJacquetBasisLift : Index → G₀ :=
  sourceRetainedBasisLift v

def sourceKPAdelicOutgoingRetainedJacquetBasisCoordinate (k : Index) : W →ₗ[ℂ] ℂ :=
  sourceRetainedCoordinate v k

theorem sourceKPAdelicOutgoingRetainedJacquetBasisCoordinate_on_lift (j k : Index) :
    sourceKPAdelicOutgoingRetainedJacquetBasisCoordinate K hζ P hs j
      (v (sourceKPAdelicOutgoingRetainedJacquetBasisLift K hζ P hs k)) =
        if j = k then 1 else 0 :=
  sourceRetainedCoordinate_on_basisLift v j k

theorem sourceKPAdelicOutgoingRetainedJacquetBasisIndex_card_le :
    Nat.card Index ≤ Nat.card (SourceKPLocalCompactProductLabel K hζ S₀) := by
  rw [Nat.card_fin]
  exact (Submodule.finrank_le _).trans
    (sourceKPAdelicOutgoingRegularizedRetainedCarrier_finrank_le K hζ S₀ s₀ hs)

abbrev SourceKPAdelicOutgoingRetainedJacquetLabel
    (places : Finset (HeightOneSpectrum (𝓞 K))) :=
  (Q : ↥places) → SourceKPAdelicOutgoingRetainedJacquetBasisIndex K hζ Q.val hs

theorem sourceKPAdelicOutgoingRetainedJacquetLabel_finite
    (places : Finset (HeightOneSpectrum (𝓞 K))) :
    Finite (SourceKPAdelicOutgoingRetainedJacquetLabel K hζ hs places) := inferInstance

end
end ArtinMatthews
