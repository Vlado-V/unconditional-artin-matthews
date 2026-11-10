module

public import ArtinMatthews.SLocalLogarithm
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
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
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourcePhysical
open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion IsDedekindDomain
open scoped NumberField BigOperators Classical
noncomputable section

variable {K : Type} [Field K]
variable {v : InfinitePlace K} (hv : IsComplex v)

/-- At a chosen complex place, the normalized local norm of this unit is `exp t`. -/
def sourceComplexPlaceRadialUnit (t : ℝ) : v.Completionˣ :=
  Units.map (ringEquivComplexOfIsComplex hv).symm.toMonoidHom
    (Units.mk0 (Real.exp (t / 2) : ℂ) (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)))

theorem sourceComplexPlaceRadialUnit_norm (t : ℝ) :
    ‖(sourceComplexPlaceRadialUnit hv t : v.Completion)‖ = Real.exp (t / 2) := by
  change ‖(ringEquivComplexOfIsComplex hv).symm (Real.exp (t / 2) : ℂ)‖ = _
  have hzero : (isometryEquivComplexOfIsComplex hv).symm (0 : ℂ) = 0 :=
    map_zero (ringEquivComplexOfIsComplex hv).symm
  have hn (z : ℂ) : ‖(ringEquivComplexOfIsComplex hv).symm z‖ = ‖z‖ :=
    (isometryEquivComplexOfIsComplex hv).symm.isometry.norm_map_of_map_zero hzero z
  rw [hn, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

theorem sourceComplexPlaceRadialUnit_zero : sourceComplexPlaceRadialUnit hv 0 = 1 := by
  apply Units.ext
  change (ringEquivComplexOfIsComplex hv).symm (Real.exp (0 / 2) : ℂ) = 1
  simp

theorem sourceComplexPlaceRadialUnit_add (a b : ℝ) :
    sourceComplexPlaceRadialUnit hv (a + b) =
      sourceComplexPlaceRadialUnit hv a * sourceComplexPlaceRadialUnit hv b := by
  apply Units.ext
  change (ringEquivComplexOfIsComplex hv).symm (Real.exp ((a + b) / 2) : ℂ) =
    (ringEquivComplexOfIsComplex hv).symm (Real.exp (a / 2) : ℂ) *
      (ringEquivComplexOfIsComplex hv).symm (Real.exp (b / 2) : ℂ)
  rw [add_div, Real.exp_add, Complex.ofReal_mul, map_mul]

variable [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))

/-- A section of the literal S-local norm, supported at a single complex place. -/
def sourceSLocalRadial (t : ℝ) : SWholeUnits K S :=
  (Pi.mulSingle v (sourceComplexPlaceRadialUnit hv t), 1)

theorem sourceSLocalRadial_zero : sourceSLocalRadial hv S 0 = 1 := by
  simp [sourceSLocalRadial, sourceComplexPlaceRadialUnit_zero]

theorem sourceSLocalRadial_add (a b : ℝ) :
    sourceSLocalRadial hv S (a + b) = sourceSLocalRadial hv S a * sourceSLocalRadial hv S b := by
  simp [sourceSLocalRadial, sourceComplexPlaceRadialUnit_add, Pi.mulSingle_mul]

theorem sourceSLocalRadial_norm (t : ℝ) : sLocalNorm K S (sourceSLocalRadial hv S t) = Real.exp t := by
  rw [sLocalNorm_eq_prod]
  have hw : (∏ w : InfinitePlace K, ‖(Pi.mulSingle (M := fun w => w.Completionˣ) v (sourceComplexPlaceRadialUnit hv t) w :
      w.Completion)‖ ^ w.mult) =
      ‖(sourceComplexPlaceRadialUnit hv t : v.Completion)‖ ^ v.mult := by
    rw [Finset.prod_eq_single v]
    · rw [Pi.mulSingle_eq_same]
    · intro w _ hw
      simp [Pi.mulSingle_eq_of_ne hw]
    · simp
  change (∏ w : InfinitePlace K, ‖(Pi.mulSingle (M := fun w => w.Completionˣ) v (sourceComplexPlaceRadialUnit hv t) w :
    w.Completion)‖ ^ w.mult) * (∏ p : S, ‖(1 : p.1.adicCompletion K)‖) = _
  rw [hw, sourceComplexPlaceRadialUnit_norm, hv.mult_eq_two, ← Real.exp_nat_mul]
  simp
  ring

end
end ArtinMatthews.SourcePhysical
