module

public import ArtinMatthews.SourcePoissonInfiniteRows
public import ArtinMatthews.SourceFrequencyOrbits
public import ArtinMatthews.SourcePrincipalDoubleResidue
public import ArtinMatthews.SourceProbeW1Mellin
public import ArtinMatthews.SourceSLocalProbeHolomorphic
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The original principal row and its exact physical Mellin weight. -/

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators MeasureTheory Set
open VaryingKummerAnalytic QuadraticWeil SourcePhysical
open scoped NumberField Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
variable {J : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F J)
variable (v : InfinitePlace F)
local notation "S" => sourceHilbertSet F S₀

/-- The source Mellin prefactor, with the actual Gaussian and both constructed weights. -/
def sourcePrincipalPoissonWeight (X Y Z : ℝ) (q : ProbeCoordinates) : ℂ :=
  (X : ℂ) ^ (1 / 2 - q.2.2) * (Z : ℂ) ^ (q.1 + q.2.2 - 1) * (Y : ℂ) ^ (q.2.1 - 1) *
    Complex.exp ((q.1 + q.2.2 - 1) ^ 2) *
    sourceSLocalProbeMellin F hζ S v q.2.2 * sourceProbeW1Mellin q.2.1

def sourcePrincipalPoissonKernel (X Y Z : ℝ) (q : ProbeCoordinates) : ℂ :=
  sourcePrincipalPoissonWeight F hζ S₀ v X Y Z q * sourcePrincipalEulerExtension F hζ S₀ η q

theorem sourcePrincipalPoissonWeight_differentiableOn_path
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {D : Set E}
    {X Y Z : ℝ} (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (p : E → ProbeCoordinates) (hp : DifferentiableOn ℂ p D)
    (hz : ∀ x ∈ D, 0 < (p x).2.2.re) :
    DifferentiableOn ℂ (fun x => sourcePrincipalPoissonWeight F hζ S₀ v X Y Z (p x)) D := by
  have hx : DifferentiableOn ℂ (fun x => (X : ℂ) ^ (1 / 2 - (p x).2.2)) D :=
    ((differentiableOn_const (1 / 2 : ℂ)).sub hp.snd.snd).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hX.ne'))
  have hξz : DifferentiableOn ℂ (fun x => (p x).1 + (p x).2.2 - 1) D :=
    (hp.fst.add hp.snd.snd).sub_const 1
  have hZ' : DifferentiableOn ℂ (fun x => (Z : ℂ) ^ ((p x).1 + (p x).2.2 - 1)) D :=
    hξz.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hZ.ne'))
  have hy : DifferentiableOn ℂ (fun x => (Y : ℂ) ^ ((p x).2.1 - 1)) D :=
    (hp.snd.fst.sub_const 1).const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hY.ne'))
  have hM : DifferentiableOn ℂ (fun x => sourceSLocalProbeMellin F hζ S v (p x).2.2) D :=
    (sourceSLocalProbeMellin_analyticOnNhd F hζ S v).differentiableOn.comp hp.snd.snd hz
  have hW : DifferentiableOn ℂ (fun x => sourceProbeW1Mellin (p x).2.1) D :=
    sourceProbeW1Mellin_entire.differentiableOn.comp hp.snd.fst (mapsTo_univ _ _)
  exact ((((hx.mul hZ').mul hy).mul (hξz.pow 2).cexp).mul hM).mul hW

theorem sourcePrincipalPoissonFrequencyNorm :
    sourcePoissonFrequencyNorm F S₀
      (sourceFrequencyRepresentative F hζ S₀ (sourceFrequencyPrincipalIndex F S₀)) = 1 := by
  unfold sourcePoissonFrequencyNorm
  rw [show (Units.mk0
    ((sourceFrequencyRepresentative F hζ S₀ (sourceFrequencyPrincipalIndex F S₀)).val : F)
    (fun h => (sourceFrequencyRepresentative F hζ S₀ (sourceFrequencyPrincipalIndex F S₀)).property
      (Subtype.ext h)) : Fˣ) = 1 by
        apply Units.ext
        simp only [Units.val_mk0, sourceFrequencyRepresentative_principal, Subalgebra.coe_one,
          Units.val_one]]
  exact map_one _

variable [IsTotallyComplex F]

/-- The continued kernel agrees pointwise with the original selected principal row. -/
theorem sourcePrincipalPoissonKernel_initial
    (hS : standardWeilBadPlaces F ⊆ S) (hcut : probePrimeCutoff F ⊆ S)
    (X Y Z : ℝ) (p : SourcePoissonHeights) :
    sourcePrincipalPoissonKernel F hζ S₀ η v X Y Z
      (sourcePoissonVertical 4 p.2, sourcePoissonVertical 4 p.1.1, sourcePoissonVertical 2 p.1.2) =
    sourcePoissonTripleKernel X Y Z 4 4 2
      (fun t => sourceProbeW1Mellin (sourcePoissonVertical 4 t))
      (fun t => sourceSLocalProbeMellin F hζ S v (sourcePoissonVertical 2 t))
      (sourcePoissonOneRow F S₀ hζ hS η
        (sourceFrequencyRepresentative F hζ S₀ (sourceFrequencyPrincipalIndex F S₀))) p := by
  unfold sourcePrincipalPoissonKernel sourcePrincipalPoissonWeight sourcePoissonTripleKernel sourcePoissonOneRow
  simp only [sourcePrincipalPoissonFrequencyNorm, Complex.ofReal_one, Complex.one_cpow, one_mul,
    sourceFrequencyRepresentative_principal]
  rw [sourcePrincipalEulerExtension_initial F hζ S₀ η hS hcut _ _ _
    (by norm_num [sourcePoissonVertical_re]) (by norm_num [sourcePoissonVertical_re])
    (by norm_num [sourcePoissonVertical_re])]

end
end ArtinMatthews.SourceEulerAssembly
