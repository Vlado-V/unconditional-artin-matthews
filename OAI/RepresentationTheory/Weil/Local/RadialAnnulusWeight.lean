module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.RepresentationTheory.Weil.Local.PlanarRadialTransfer
public import OAI.RepresentationTheory.Weil.Local.RadialTailCutoffBound
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import OAI.RepresentationTheory.Weil.Local.PlanarCompactTransfer
public import OAI.RepresentationTheory.Weil.Local.RadialTailSmooth


set_option backward.privateInPublic true
@[expose] public section

/-! # Radial Annulus Weight -/

namespace OAI.RepresentationTheory.Weil.Local.RadialAnnulusWeight.Construction

noncomputable section

/-! Compact annular approximations to the actual radial tail weight. -/

open Set
open scoped ContDiff

def radialAnnulusWeight (s ε R T t : ℝ) : ℝ :=
  (1 - RadialTailCutoffBound.Construction.radialCutoff T t) * RadialTailCutoffBound.Construction.radialTailWeight s ε R t

def radialAnnulusWeightDerivative (s ε R T t : ℝ) : ℝ :=
  -RadialTailCutoffBound.Construction.radialCutoffDerivative T t * RadialTailCutoffBound.Construction.radialTailWeight s ε R t +
    (1 - RadialTailCutoffBound.Construction.radialCutoff T t) * RadialTailCutoffBound.Construction.radialTailWeightDerivative s ε R t

def radialAnnulusWeightSecondDerivative (s ε R T t : ℝ) : ℝ :=
  -RadialTailCutoffBound.Construction.radialCutoffSecondDerivative T t * RadialTailCutoffBound.Construction.radialTailWeight s ε R t -
    2 * RadialTailCutoffBound.Construction.radialCutoffDerivative T t * RadialTailCutoffBound.Construction.radialTailWeightDerivative s ε R t +
    (1 - RadialTailCutoffBound.Construction.radialCutoff T t) * RadialTailCutoffBound.Construction.radialTailWeightSecondDerivative s ε R t

theorem radialAnnulusWeight_contDiff (s ε R T : ℝ) (hR : 0 < R) :
    ContDiff ℝ ∞ (radialAnnulusWeight s ε R T) :=
  (contDiff_const.sub (RadialTailSmooth.Construction.radialCutoff_contDiff T)).mul (RadialTailSmooth.Construction.radialTailWeight_contDiff s ε R hR)

theorem radialAnnulusWeight_hasDerivAt (s ε R T : ℝ) (hR : 0 < R) (t : ℝ) :
    HasDerivAt (radialAnnulusWeight s ε R T) (radialAnnulusWeightDerivative s ε R T t) t := by
  exact ((RadialTailCutoffBound.Construction.radialCutoff_hasDerivAt T t).const_sub 1).mul (RadialTailCutoffBound.Construction.radialTailWeight_hasDerivAt s ε R hR t)

theorem radialAnnulusWeightDerivative_hasDerivAt (s ε R T : ℝ) (hR : 0 < R) (t : ℝ) :
    HasDerivAt (radialAnnulusWeightDerivative s ε R T)
      (radialAnnulusWeightSecondDerivative s ε R T t) t := by
  have hd := (((RadialTailCutoffBound.Construction.radialCutoffDerivative_hasDerivAt T t).neg).mul
    (RadialTailCutoffBound.Construction.radialTailWeight_hasDerivAt s ε R hR t)).add
      (((RadialTailCutoffBound.Construction.radialCutoff_hasDerivAt T t).const_sub 1).mul (RadialTailCutoffBound.Construction.radialTailWeightDerivative_hasDerivAt s ε R hR t))
  dsimp only [Pi.neg_apply] at hd
  convert! hd using 1
  unfold radialAnnulusWeightSecondDerivative
  ring

theorem radialAnnulusWeight_upper_zero (s ε R T t : ℝ) (hT : 0 < T) (ht : 2 * T ≤ t) :
    radialAnnulusWeight s ε R T t = 0 := by
  rw [radialAnnulusWeight, RadialTailCutoffBound.Construction.radialCutoff_one T t hT ht, sub_self, zero_mul]

theorem radialAnnulusWeight_lower_zero (s ε R T t : ℝ) (hR : 0 < R) (ht : t < R) :
    radialAnnulusWeight s ε R T t = 0 ∧ radialAnnulusWeightDerivative s ε R T t = 0 ∧
      radialAnnulusWeightSecondDerivative s ε R T t = 0 := by
  simp only [radialAnnulusWeight, radialAnnulusWeightDerivative, radialAnnulusWeightSecondDerivative,
    RadialTailCutoffBound.Construction.radialTailWeight_zero s ε R t hR ht, RadialTailCutoffBound.Construction.radialTailWeightDerivative_zero s ε R t hR ht,
    RadialTailCutoffBound.Construction.radialTailWeightSecondDerivative_zero s ε R t hR ht, mul_zero, add_zero, sub_zero, and_self]

theorem radialAnnulusWeight_laplacian (s ε R T t : ℝ) :
    t * radialAnnulusWeightSecondDerivative s ε R T t + radialAnnulusWeightDerivative s ε R T t =
      (1 - RadialTailCutoffBound.Construction.radialCutoff T t) *
        (t * RadialTailCutoffBound.Construction.radialTailWeightSecondDerivative s ε R t + RadialTailCutoffBound.Construction.radialTailWeightDerivative s ε R t) -
      2 * t * RadialTailCutoffBound.Construction.radialCutoffDerivative T t * RadialTailCutoffBound.Construction.radialTailWeightDerivative s ε R t -
      (t * RadialTailCutoffBound.Construction.radialCutoffSecondDerivative T t + RadialTailCutoffBound.Construction.radialCutoffDerivative T t) * RadialTailCutoffBound.Construction.radialTailWeight s ε R t := by
  unfold radialAnnulusWeightSecondDerivative radialAnnulusWeightDerivative
  ring

theorem radialAnnulusWeight_complex_deriv (s ε R T : ℝ) (hR : 0 < R) :
    deriv (fun t => (radialAnnulusWeight s ε R T t : ℂ)) =
      fun t => (radialAnnulusWeightDerivative s ε R T t : ℂ) :=
  funext fun t => ((radialAnnulusWeight_hasDerivAt s ε R T hR t).ofReal_comp).deriv

theorem radialAnnulusWeight_complex_second_deriv (s ε R T : ℝ) (hR : 0 < R) :
    deriv (deriv (fun t => (radialAnnulusWeight s ε R T t : ℂ))) =
      fun t => (radialAnnulusWeightSecondDerivative s ε R T t : ℂ) := by
  rw [radialAnnulusWeight_complex_deriv s ε R T hR]
  exact funext fun t => ((radialAnnulusWeightDerivative_hasDerivAt s ε R T hR t).ofReal_comp).deriv

theorem radialAnnulusWeight_transfer_integrable (s ε R T b : ℝ) (hR : 0 < R) (hT : 0 < T) :
    PlanarRadialTransfer.Construction.planarRadialTransferIntegrable b (fun t => (radialAnnulusWeight s ε R T t : ℂ))
      (fun t => (radialAnnulusWeightDerivative s ε R T t : ℂ))
      (fun t => (radialAnnulusWeightSecondDerivative s ε R T t : ℂ)) := by
  have hc : ContDiff ℝ ∞ (fun t => (radialAnnulusWeight s ε R T t : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (radialAnnulusWeight_contDiff s ε R T hR)
  have hs : Function.support (fun t => (radialAnnulusWeight s ε R T t : ℂ)) ⊆ Iic (2 * T) := by
    intro t ht
    by_contra hh
    apply ht
    dsimp only
    rw [radialAnnulusWeight_upper_zero s ε R T t hT (le_of_not_ge hh)]
    rfl
  have hi := PlanarCompactTransfer.Construction.planarRadialTransferIntegrable_of_compact b _ hc (2 * T) hs
  rwa [radialAnnulusWeight_complex_second_deriv s ε R T hR,
    radialAnnulusWeight_complex_deriv s ε R T hR] at hi

end

end OAI.RepresentationTheory.Weil.Local.RadialAnnulusWeight.Construction
