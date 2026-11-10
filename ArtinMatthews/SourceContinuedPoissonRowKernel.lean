module

public import ArtinMatthews.SourcePoissonInitialRows
public import ArtinMatthews.SourceProbeW1Mellin
public import ArtinMatthews.SourcePoissonTripleKernel
public import ArtinMatthews.SourceRowEulerHolomorphy
public import ArtinMatthews.SourceSLocalProbeMellin
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

/-! The literal continued source row, with the physical Mellin weights,
frequency power and Gaussian. On the three initial lines it is exactly
one summand of the original Poisson kernel. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain MeasureTheory AllowedGenerators Set
open VaryingKummerAnalytic QuadraticWeil SourcePhysical
open scoped NumberField Classical BigOperators
noncomputable section
variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable {J : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F J) (hJ : J ≠ ⊥)
local notation "S" => sourceHilbertSet F S₀
local notation "R" => sourceRing F S₀

/-- The weighted row uses the same field S-norm as the initial Poisson formula. -/
def sourceContinuedPoissonRowKernel (v : InfinitePlace F) (u : {a : R // a ≠ 0})
    (X Y Z : ℝ) (p : ProbeCoordinates) : ℂ :=
  (X : ℂ)^(1/2-p.2.2) * (Z : ℂ)^(p.1+p.2.2-1) * (Y : ℂ)^(p.2.1-1) *
    Complex.exp ((p.1+p.2.2-1)^2) * sourceSLocalProbeMellin F hζ S v p.2.2 *
    sourceProbeW1Mellin p.2.1 *
    ((sourcePoissonFrequencyNorm F S₀ u : ℂ)^(-p.2.2) *
      sourceRowEulerContinuation F hζ S₀ u.val u.property η hJ p)

theorem sourceContinuedPoissonRowKernel_initial
    (hS : standardWeilBadPlaces F ⊆ S) (hcut : probePrimeCutoff F ⊆ S)
    (v : InfinitePlace F) (u : {a : R // a ≠ 0}) (X Y Z : ℝ) (p : SourcePoissonHeights) :
    sourceContinuedPoissonRowKernel F S₀ hζ η hJ v u X Y Z
      (sourcePoissonVertical 4 p.2, sourcePoissonVertical 4 p.1.1, sourcePoissonVertical 2 p.1.2) =
      sourcePoissonTripleKernel X Y Z 4 4 2
        (fun t => sourceProbeW1Mellin (sourcePoissonVertical 4 t))
        (fun t => sourceSLocalProbeMellin F hζ S v (sourcePoissonVertical 2 t))
        (sourcePoissonInitialRows F S₀ hζ hS η {u}) p := by
  unfold sourceContinuedPoissonRowKernel sourcePoissonTripleKernel sourcePoissonInitialRows
  simp only [Finset.sum_singleton]
  rw [sourceRowEulerContinuation_initial F hζ S₀ u.val u.property η hJ hS hcut _ _ _
    (by norm_num [sourcePoissonVertical_re]) (by norm_num [sourcePoissonVertical_re])
    (by norm_num [sourcePoissonVertical_re])]

theorem sourceContinuedPoissonRowKernel_differentiableOn_path
    (hcut : principalAngularCutoff F J ⊆ S) (v : InfinitePlace F) (u : {a : R // a ≠ 0})
    (hu : ¬ ∃ a : F, a^6 = (u.val : F))
    {X Y Z : ℝ} (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    {D : Set ℂ} (p : ℂ → ProbeCoordinates) (hp : DifferentiableOn ℂ p D)
    (hmem : MapsTo p D (sourceRowEulerOpenDomain F hζ S₀ u.val u.property η hJ))
    (hz : ∀ x ∈ D, 0 < (p x).2.2.re) :
    DifferentiableOn ℂ (fun x => sourceContinuedPoissonRowKernel F S₀ hζ η hJ v u X Y Z (p x)) D := by
  have hx : DifferentiableOn ℂ (fun x => (X : ℂ)^(1/2-(p x).2.2)) D :=
    ((differentiableOn_const (1/2 : ℂ)).sub hp.snd.snd).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hX.ne'))
  have hξz : DifferentiableOn ℂ (fun x => (p x).1+(p x).2.2-1) D :=
    (hp.fst.add hp.snd.snd).sub_const 1
  have hZ' : DifferentiableOn ℂ (fun x => (Z : ℂ)^((p x).1+(p x).2.2-1)) D :=
    hξz.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hZ.ne'))
  have hy : DifferentiableOn ℂ (fun x => (Y : ℂ)^((p x).2.1-1)) D :=
    (hp.snd.fst.sub_const 1).const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hY.ne'))
  have hM : DifferentiableOn ℂ (fun x => sourceSLocalProbeMellin F hζ S v (p x).2.2) D :=
    (sourceSLocalProbeMellin_analyticOnNhd F hζ S v).differentiableOn.comp hp.snd.snd hz
  have hW : DifferentiableOn ℂ (fun x => sourceProbeW1Mellin (p x).2.1) D :=
    sourceProbeW1Mellin_entire.differentiableOn.comp hp.snd.fst (mapsTo_univ _ _)
  have hq : DifferentiableOn ℂ (fun x => (sourcePoissonFrequencyNorm F S₀ u : ℂ)^(-(p x).2.2)) D :=
    hp.snd.snd.neg.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr (sourcePoissonFrequencyNorm_pos F S₀ u).ne'))
  have hF := (sourceRowEulerContinuation_differentiableOn F hζ S₀ u.val u.property η hJ hcut hu).comp hp hmem
  exact ((((((hx.mul hZ').mul hy).mul (hξz.pow 2).cexp).mul hM).mul hW).mul (hq.mul hF))

theorem sourceContinuedPoissonRowKernel_vertical_norm
    (v : InfinitePlace F) (u : {a : R // a ≠ 0}) {X Y Z : ℝ} (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (a b c : ℝ) (p : SourcePoissonHeights) :
    let ξ := sourcePoissonVertical a p.2
    let w := sourcePoissonVertical b p.1.1
    let z := sourcePoissonVertical c p.1.2
    ‖sourceContinuedPoissonRowKernel F S₀ hζ η hJ v u X Y Z (ξ,w,z)‖ =
      (sourcePoissonTripleScale X Y Z a b c *
        ‖(sourcePoissonFrequencyNorm F S₀ u : ℂ)^(-z)*
          sourceRowEulerContinuation F hζ S₀ u.val u.property η hJ (ξ,w,z)‖) *
      ((‖sourceProbeW1Mellin w‖*‖sourceSLocalProbeMellin F hζ S v z‖) *
        Real.exp (-((p.2+p.1.2)^2))) :=
  sourcePoissonTripleKernel_norm hX hY hZ a b c
    (fun t => sourceProbeW1Mellin (sourcePoissonVertical b t))
    (fun t => sourceSLocalProbeMellin F hζ S v (sourcePoissonVertical c t))
    (fun x => (sourcePoissonFrequencyNorm F S₀ u : ℂ)^(-sourcePoissonVertical c x.1.2)*
      sourceRowEulerContinuation F hζ S₀ u.val u.property η hJ
        (sourcePoissonVertical a x.2, sourcePoissonVertical b x.1.1, sourcePoissonVertical c x.1.2)) p

end
end ArtinMatthews.SourceEulerAssembly
