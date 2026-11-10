module

public import ArtinMatthews.SourceSLocalRadialSection
public import ArtinMatthews.SLocalNormOneGroup
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
open NumberField NumberField.InfinitePlace IsDedekindDomain
open scoped NumberField BigOperators Classical
noncomputable section

variable {K : Type} [Field K] [NumberField K]
variable {v : InfinitePlace K} (hv : IsComplex v)
variable (S : Finset (HeightOneSpectrum (𝓞 K)))

def sourceSLocalLogNorm (x : SWholeUnits K S) : ℝ :=
  sLocalLogSum K S (Additive.ofMul x)

theorem sourceSLocalLogNorm_mul (x y : SWholeUnits K S) :
    sourceSLocalLogNorm S (x * y) = sourceSLocalLogNorm S x + sourceSLocalLogNorm S y :=
  map_add (sLocalLogSum K S) (Additive.ofMul x) (Additive.ofMul y)

theorem sourceSLocalLogNorm_radial (t : ℝ) :
    sourceSLocalLogNorm S (sourceSLocalRadial hv S t) = t :=
  Real.exp_injective (sourceSLocalRadial_norm hv S t)

theorem sourceSLocalLogNorm_normOne (x : SNormOne K S) :
    sourceSLocalLogNorm S (x : SWholeUnits K S) = 0 :=
  (sLocalNorm_eq_one_iff K S x).mp x.property

def sourceSLocalRadialProjection (x : SWholeUnits K S) : SNormOne K S :=
  ⟨x * (sourceSLocalRadial hv S (sourceSLocalLogNorm S x))⁻¹, by
    change sLocalNorm K S (x * (sourceSLocalRadial hv S (sourceSLocalLogNorm S x))⁻¹) = 1
    rw [sLocalNorm_mul, sLocalNorm_inv, sourceSLocalRadial_norm]
    exact mul_inv_cancel₀ (Real.exp_ne_zero _)⟩

/-- The actual S-local unit group splits as its norm-one group times the logarithmic real line. -/
def sourceSLocalRadialMulEquiv : SNormOne K S × Multiplicative ℝ ≃* SWholeUnits K S where
  toFun x := (x.1 : SWholeUnits K S) * sourceSLocalRadial hv S x.2.toAdd
  invFun x := (sourceSLocalRadialProjection hv S x, Multiplicative.ofAdd (sourceSLocalLogNorm S x))
  left_inv x := by
    rcases x with ⟨u,t⟩
    have hlog : sourceSLocalLogNorm S ((u : SWholeUnits K S) *
        sourceSLocalRadial hv S t.toAdd) = t.toAdd := by
      rw [sourceSLocalLogNorm_mul, sourceSLocalLogNorm_normOne, sourceSLocalLogNorm_radial, zero_add]
    apply Prod.ext
    · apply Subtype.ext
      change (u : SWholeUnits K S) * sourceSLocalRadial hv S t.toAdd *
        (sourceSLocalRadial hv S (sourceSLocalLogNorm S
          ((u : SWholeUnits K S) * sourceSLocalRadial hv S t.toAdd)))⁻¹ = u
      rw [hlog, mul_inv_cancel_right]
    · exact congrArg Multiplicative.ofAdd hlog
  right_inv x := by
    change x * (sourceSLocalRadial hv S (sourceSLocalLogNorm S x))⁻¹ *
      sourceSLocalRadial hv S (sourceSLocalLogNorm S x) = x
    exact inv_mul_cancel_right _ _
  map_mul' x y := by
    change ((x.1 : SWholeUnits K S) * (y.1 : SWholeUnits K S)) *
        sourceSLocalRadial hv S (x.2.toAdd + y.2.toAdd) =
      ((x.1 : SWholeUnits K S) * sourceSLocalRadial hv S x.2.toAdd) *
        ((y.1 : SWholeUnits K S) * sourceSLocalRadial hv S y.2.toAdd)
    rw [sourceSLocalRadial_add]
    ac_rfl

theorem sourceSLocalRadialMulEquiv_norm (x : SNormOne K S × Multiplicative ℝ) :
    sLocalNorm K S (sourceSLocalRadialMulEquiv hv S x) = Real.exp x.2.toAdd := by
  change sLocalNorm K S ((x.1 : SWholeUnits K S) * sourceSLocalRadial hv S x.2.toAdd) = _
  rw [sLocalNorm_mul, sourceSLocalRadial_norm, show sLocalNorm K S x.1 = 1 from x.1.property,
    one_mul]

end
end ArtinMatthews.SourcePhysical
