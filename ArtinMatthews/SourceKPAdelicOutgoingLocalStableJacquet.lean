module

public import ArtinMatthews.SourceKPAdelicOutgoingLocalCyclic
public import ArtinMatthews.SourceKPJacquetDeepSmooth
public import ArtinMatthews.SourceKPJacquetCovariance
public import ArtinMatthews.SourceKPJacquetKernel
public import ArtinMatthews.SourceKPJacquetTinyUnits
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
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.TotallySplit
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

/-! The stable Jacquet map on the actual outgoing cyclic space takes
values in its finite all-remainder Borel carrier. Deep smoothness and
the upper and unit-cube laws follow from the actual outgoing section. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain StandardAdelic SourcePhysical
open scoped Classical SourcePhysical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K))

local notation "S" => (Singleton.singleton P : Finset (HeightOneSpectrum (𝓞 K)))
local notation "G₀" => SourceFiniteKP2Projective K hζ P
local notation "B₀" => SourceFiniteKPProjectiveBorel K hζ P
local notation "L" => P.adicCompletion K
local notation "V" => SourceKPAdelicTorusInducedSpace K hζ
local notation "W" => sourceKPAdelicOutgoingRegularizedRetainedCarrier K hζ S
local notation "R₀" => sourceKPAdelicOutgoingRegularizedLocalSection K hζ P
local notation "ρ₀" => sourceKPAdelicOutgoingRegularizedLocalBorelRepresentation K hζ P
local notation "C" => sourceKPAdelicOutgoingRegularizedLocalCyclic K hζ P
local notation "n₀" => (fun x : L => sourceFiniteKP2ProjectiveLift K hζ P (sourceGL2Upper x))
local notation "ψ₀" => localFiniteCharacter K P

local instance sourceKPAdelicOutgoingLocalJacquetTorusAddCommGroup (s : ℂ) :
    AddCommGroup (V s) := Submodule.addCommGroup _

local instance sourceKPAdelicOutgoingLocalJacquetCarrierAddCommGroup (s : ℂ) (hs : 0 < s.re) :
    AddCommGroup (W s hs) := Submodule.addCommGroup _

theorem sourceKPAdelicOutgoingRegularizedLocalCyclic_le_deepFixed (s : ℂ) (hs : 0 < s.re) :
    C s hs ≤ sourceKPJacquetDeepFixedSubspace K hζ P (ρ₀ s hs) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨a,rfl⟩
  exact sourceKPJacquetDeepFixedSubspace_invariant K hζ P (ρ₀ s hs) a (R₀ s hs).val
    ((sourceKPLocalCompactFixedSpace_le_jacquetDeepFixed K hζ P (ρ₀ s hs)) (R₀ s hs).property)

theorem sourceKPAdelicOutgoingRegularizedLocalJacquet_rootSmooth (s : ℂ) (hs : 0 < s.re) :
    SourceKPJacquetRootSmooth K hζ P (ρ₀ s hs) (C s hs) :=
  sourceKPJacquet_rootSmooth_of_deepFixed K hζ P (ρ₀ s hs) (C s hs)
    (sourceKPAdelicOutgoingRegularizedLocalCyclic_le_deepFixed K hζ P s hs)

theorem sourceKPAdelicOutgoingRegularizedLocalBorelRepresentation_unit_cube_fixed
    (s : ℂ) (hs : 0 < s.re) (u : Lˣ)
    (hu : sourceLocalValuation K P (((u ^ 3 : Lˣ) : L)) = 1) (v : W s hs) :
    ρ₀ s hs (sourceFiniteKPProjectiveBorelDiagonal K hζ P (u^3)) v = v := by
  apply Subtype.ext
  funext r
  rw [sourceKPAdelicOutgoingRegularizedLocalBorelRepresentation_apply K hζ P]
  exact sourceKPJacquet_actual_unit_cube_fixed K P hζ (-s) u hu (v.val r)

def sourceKPAdelicOutgoingRegularizedLocalJacquetCoordinates (s : ℂ) (hs : 0 < s.re) :
    W s hs ≃ₗ[ℂ] (Fin (Module.finrank ℂ (W s hs)) → ℂ) := by
  let : FiniteDimensional ℂ (W s hs) :=
    sourceKPAdelicOutgoingRegularizedLocalCarrier_finiteDimensional K hζ P s hs
  exact (Module.finBasis ℂ (W s hs)).equivFun

local notation "e" => sourceKPAdelicOutgoingRegularizedLocalJacquetCoordinates K hζ P
local notation "hU" => sourceKPAdelicOutgoingRegularizedLocalBorelRepresentation_upper K hζ P
local notation "hD" => sourceKPAdelicOutgoingRegularizedLocalBorelRepresentation_unit_cube_fixed K hζ P
local notation "hS" => sourceKPAdelicOutgoingRegularizedLocalJacquet_rootSmooth K hζ P
local notation "hC" => sourceKPAdelicOutgoingRegularizedLocalCyclic_invariant K hζ P

def sourceKPAdelicOutgoingRegularizedLocalJacquetMap (s : ℂ) (hs : 0 < s.re) :
    C s hs →ₗ[ℂ] W s hs :=
  sourceKPJacquetStableMap K hζ P (ρ₀ s hs) (C s hs) (e s hs) (hU s hs) (hD s hs) (hS s hs)

local notation "J" => sourceKPAdelicOutgoingRegularizedLocalJacquetMap K hζ P
local notation "π" =>
  (fun (s : ℂ) (hs : 0 < Complex.re s) =>
    sourceKPJacquetRight K hζ P (ρ₀ s hs) (C s hs) (hC s hs))

theorem sourceKPAdelicOutgoingRegularizedLocalJacquetMap_hasStableValue
    (s : ℂ) (hs : 0 < s.re) (f : C s hs) :
    SourceKPJacquetHasStableValue K hζ P (ρ₀ s hs) (C s hs) (e s hs) f (J s hs f) :=
  sourceKPJacquetStableMap_hasStableValue K hζ P (ρ₀ s hs) (C s hs) (e s hs)
    (hU s hs) (hD s hs) (hS s hs) f

theorem sourceKPAdelicOutgoingRegularizedLocalJacquetMap_upper
    (s : ℂ) (hs : 0 < s.re) (x : L) (f : C s hs) :
    J s hs (π s hs (n₀ x) f) = ψ₀ x • J s hs f :=
  sourceKPJacquetStableMap_upper K hζ P (ρ₀ s hs) (C s hs) (e s hs)
    (hU s hs) (hD s hs) (hS s hs) (hC s hs) x f

theorem sourceKPAdelicOutgoingRegularizedLocalJacquetMap_whittaker_factors
    (s : ℂ) (hs : 0 < s.re) (ℓ : C s hs →ₗ[ℂ] ℂ)
    (hℓ : ∀ (x : L) (f : C s hs), ℓ (π s hs (n₀ x) f) = ψ₀ x * ℓ f) :
    SourceKPJacquetFactors (X := C s hs) (Y := W s hs) (J s hs) ℓ :=
  sourceKPJacquetFactors_of_ker_le (X := C s hs) (Y := W s hs) (J s hs) ℓ
    (sourceKPJacquet_kernel_le_whittaker_kernel K hζ P (ρ₀ s hs) (C s hs) (e s hs)
      (hC s hs) (hU s hs) (hD s hs) (hS s hs) ℓ hℓ)

end
end ArtinMatthews
