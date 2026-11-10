module

public import ArtinMatthews.SourceSLocalRadialCoordinates
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourcePhysical
open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion IsDedekindDomain
open scoped NumberField BigOperators Classical
noncomputable section

variable {K : Type} [Field K]
variable {v : InfinitePlace K} (hv : IsComplex v)

theorem sourceComplexPlaceRadialUnit_continuous : Continuous (sourceComplexPlaceRadialUnit hv) := by
  apply Units.continuous_iff.mpr
  have h : Continuous (fun t : ℝ => (Real.exp (t / 2) : ℂ)) :=
    Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_id.div_const 2))
  have hc : Continuous (ringEquivComplexOfIsComplex hv).symm :=
    (isometryEquivComplexOfIsComplex hv).symm.continuous
  have hm : Continuous (fun t : ℝ => (sourceComplexPlaceRadialUnit hv t : v.Completion)) :=
    hc.comp h
  refine ⟨hm, ?_⟩
  have hi : Continuous (fun t : ℝ => (sourceComplexPlaceRadialUnit hv t : v.Completion)⁻¹) :=
    hm.inv₀ (fun t => (sourceComplexPlaceRadialUnit hv t).ne_zero)
  simpa only [Units.val_inv_eq_inv_val] using hi

variable [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))

theorem sourceSLocalRadial_continuous : Continuous (sourceSLocalRadial hv S) := by
  refine (continuous_pi fun w => ?_).prodMk continuous_const
  by_cases h : w = v
  · subst w
    simpa only [Pi.mulSingle_eq_same] using sourceComplexPlaceRadialUnit_continuous hv
  · simpa only [Pi.mulSingle_eq_of_ne h] using
      (continuous_const : Continuous (fun _ : ℝ => (1 : w.Completionˣ)))

theorem sourceSLocalRadialProjection_continuous :
    Continuous (sourceSLocalRadialProjection hv S) := by
  apply Continuous.subtype_mk
  exact continuous_id.mul ((sourceSLocalRadial_continuous hv S).comp
    (continuous_sLocalLogSum K S)).inv

/-- The algebraic radial factorization is a homeomorphism for the actual S-local topology. -/
def sourceSLocalRadialHomeomorph : SNormOne K S × Multiplicative ℝ ≃ₜ SWholeUnits K S where
  toEquiv := (sourceSLocalRadialMulEquiv hv S).toEquiv
  continuous_toFun := by
    change Continuous (fun x : SNormOne K S × Multiplicative ℝ =>
      (x.1 : SWholeUnits K S) * sourceSLocalRadial hv S x.2.toAdd)
    exact (continuous_subtype_val.comp continuous_fst).mul
      ((sourceSLocalRadial_continuous hv S).comp continuous_snd)
  continuous_invFun := by
    change Continuous (fun x : SWholeUnits K S =>
      (sourceSLocalRadialProjection hv S x, Multiplicative.ofAdd (sourceSLocalLogNorm S x)))
    exact (sourceSLocalRadialProjection_continuous hv S).prodMk (continuous_sLocalLogSum K S)

end
end ArtinMatthews.SourcePhysical
