module

public import ArtinMatthews.SourceKPAdelicExceptionalCharacter
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

/-! Exact rational compatibility of the actual global exceptional
central character. A rational projective element in the cube torus
has a principal normalized diagonal ratio and phase one. The idele
product formula gives triviality directly on that ratio. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAdelicExceptionalCharacter_rational_coordinates (g : PGL(2, K))
    (x : sourceKPAdelicCubeTorus K hζ) (hx : sourceKPAdelicProjectiveRationalLift K hζ g = x.val) :
    ∃ y : Kˣ, g = sourceKPProjectiveDiagonalHom K y ∧
      ((sourceKPAdelicCubeTorusEquiv K hζ).symm x).1 = 1 ∧
      ((sourceKPAdelicCubeTorusEquiv K hζ).symm x).2.val = IdeleGroup.unitEmbedding (𝓞 K) K y := by
  let E := sourceKPAdelicCubeTorusEquiv K hζ
  let p := E.symm x
  have hp : E p = x := E.apply_symm_apply x
  have he : sourceKPAdelicProjectiveRationalLift K hζ g = sourceKPAdelicCubeEmbedding K hζ p := by
    rw [← sourceKPAdelicCubeTorusEquiv_val]
    change sourceKPAdelicProjectiveRationalLift K hζ g = (E p).val
    rwa [hp]
  have hbase := congrArg (sourceKPAdelicProjectiveProjection K hζ) he
  rw [sourceKPAdelicProjectiveRationalLift_projection, sourceKPAdelicCubeEmbedding_projection] at hbase
  let : Nontrivial 𝔸[K] := inferInstanceAs (Nontrivial (InfiniteAdeleRing K × 𝔸ᶠ[K]))
  obtain ⟨y, hg, hy⟩ := sourceKPProjectiveDiagonalHom_rational (algebraMap K 𝔸[K]) g p.2.val hbase
  change p.2.val = IdeleGroup.unitEmbedding (𝓞 K) K y at hy
  have hr : sourceKPAdelicProjectiveRationalLift K hζ g = sourceKPAdelicProjectiveDiagonalLift K hζ p.2.val := by
    rw [hg, sourceKPAdelicProjectiveRationalLift_diagonal, hy]
  have hphase : sourceKPAdelicProjectiveCenter K hζ p.1 = 1 := by
    apply mul_right_cancel (b := sourceKPAdelicProjectiveDiagonalLift K hζ p.2.val)
    rw [one_mul]
    exact he.symm.trans hr
  have hz : p.1 = 1 := sourceKPAdelicProjectiveCenter_injective K hζ (by rw [map_one]; exact hphase)
  exact ⟨y, hg, hz, hy⟩

theorem sourceKPAdelicExceptionalCharacter_rational (g : PGL(2, K))
    (x : sourceKPAdelicCubeTorus K hζ) (hx : sourceKPAdelicProjectiveRationalLift K hζ g = x.val) :
    sourceKPAdelicExceptionalCharacter K hζ x = 1 := by
  obtain ⟨y, _, hz, hy⟩ := sourceKPAdelicExceptionalCharacter_rational_coordinates K hζ g x hx
  let E := sourceKPAdelicCubeTorusEquiv K hζ
  let p := E.symm x
  have hp : E p = x := E.apply_symm_apply x
  rw [← hp, sourceKPAdelicExceptionalCharacter_equiv]
  change p.1 = 1 at hz
  change p.2.val = IdeleGroup.unitEmbedding (𝓞 K) K y at hy
  rw [hz, map_one, one_mul, hy]
  apply Units.ext
  change ((sourceKPIdeleSixthNorm K (IdeleGroup.unitEmbedding (𝓞 K) K y) : ℂˣ) : ℂ) = 1
  rw [sourceKPIdeleSixthNorm_coe, sourceKPIdeleAbsoluteNorm_principal, Real.one_rpow, Complex.ofReal_one]

end
end ArtinMatthews
