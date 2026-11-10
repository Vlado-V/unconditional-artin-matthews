module

public import ArtinMatthews.SourceNonprincipalFrequencyDyads
public import ArtinMatthews.SourceContinuedPoissonRowIntegral
public import ArtinMatthews.SourcePoissonOrbitRows
public import ArtinMatthews.SourceContinuedPoissonRowShifts
public import ArtinMatthews.SourcePoissonActualInitialContour
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

/-! Each original physical orbit summand equals its normalized initial
continued row. Absolute summability is inherited from the actual orbit
series before any dyad is shifted. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators MeasureTheory
open VaryingKummerAnalytic QuadraticWeil SourcePhysical
open scoped NumberField Classical BigOperators ContDiff
noncomputable section
variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable {J : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F J) (hJ : J ≠ ⊥)
local notation "S" => sourceHilbertSet F S₀
local notation "R" => sourceRing F S₀
local notation "I" => sourceContinuedPoissonRowIntegral F S₀ hζ η hJ
local notation "U" => sourceFrequencyRepresentative F hζ S₀

theorem sourceContinuedPoissonRowIntegral_eq_orbitRow
    (hS : standardWeilBadPlaces F ⊆ S) (hcut : probePrimeCutoff F ⊆ S)
    (v : InfinitePlace F) (u : {a : R // a ≠ 0})
    {X Y Z : ℝ} (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) :
    I v u X Y Z 4 4 2 = ∑' a : SourceExponentCoordinates F S₀,
      sourcePoissonOrbitTerm F S₀ hζ hS η v sourceProbeW1Complex X Y Z u a := by
  rw [sourceContinuedPoissonRowIntegral_initial F S₀ hζ η hJ hS hcut v u X Y Z]
  have h := sourcePoissonOrbitRow_eq_initialContour F S₀ hζ hS η v sourceProbeW1Complex
    sourceProbeW1Complex_compact sourceProbeW1Complex_positive_support sourceProbeW1Complex_contDiff
    hX hY hZ u
  simpa only [sourcePoissonFrequencyKernel, sourcePoissonTripleKernel, sourcePoissonInitialRows,
    Finset.sum_singleton, sourceProbeW1Mellin, sourcePoissonNormalization, Complex.ofReal_div,
    Complex.ofReal_mul, Complex.ofReal_one, Complex.ofReal_ofNat, mul_assoc] using h.symm

theorem sourceContinuedPoissonInitialRows_summable_norm
    (hS : standardWeilBadPlaces F ⊆ S) (hcut : probePrimeCutoff F ⊆ S) (v : InfinitePlace F)
    {X Y Z : ℝ} (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) :
    Summable (fun i : SourceFrequencyRepresentativeIndex F S₀ => ‖I v (U i) X Y Z 4 4 2‖) := by
  have h := (sourcePoissonActualOrbitSeries_eq_initialContour F S₀ hζ hS η v hX hY hZ).2.1
  simpa only [sourceContinuedPoissonRowIntegral_eq_orbitRow F S₀ hζ η hJ hS hcut v _ hX hY hZ] using h

def sourcePoissonNonprincipalRowSeries (v : InfinitePlace F) (X Y Z : ℝ) : ℂ :=
  ∑' i : SourceNonprincipalFrequencyIndex F S₀, I v (U i.val) X Y Z 4 4 2

def sourcePoissonNonprincipalDyadSum (v : InfinitePlace F) (X Y Z : ℝ) (j : ℕ) : ℂ :=
  ∑ i : SourceNonprincipalFrequencyDyad F S₀ j, I v (U i.val.val) X Y Z 4 4 2

theorem sourcePoissonNonprincipalRowSeries_eq_dyads
    (hS : standardWeilBadPlaces F ⊆ S) (hcut : probePrimeCutoff F ⊆ S) (v : InfinitePlace F)
    {X Y Z : ℝ} (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) :
    sourcePoissonNonprincipalRowSeries F S₀ hζ η hJ v X Y Z =
      ∑' j : ℕ, sourcePoissonNonprincipalDyadSum F S₀ hζ η hJ v X Y Z j := by
  have h := (sourceContinuedPoissonInitialRows_summable_norm F S₀ hζ η hJ hS hcut v hX hY hZ).of_norm
  exact sourceNonprincipalFrequency_tsum_dyads F S₀ _ (h.subtype _)

end
end ArtinMatthews.SourceEulerAssembly
