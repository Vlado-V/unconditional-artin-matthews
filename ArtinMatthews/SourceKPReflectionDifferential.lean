module

public import ArtinMatthews.SourceKPReflectionWeyl
public import ArtinMatthews.SourceArchReflectionDifferential
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

/-! The actual signed rational rotation differentiates in each horizontal
direction by the exact reflected height and unit angular phase. -/
namespace ArtinMatthews
open NumberField SourceArchJacquet SourceHyperbolicGreen OAI.CubicEisenstein Filter
open scoped NumberField MatrixGroups AdeleRing Classical Topology ContDiff
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
local notation "V" => InfinitePlace K
local notation "X" => ProductSpace V
local notation "Ω" => productUpper V
local notation "σ" => sourceKPCuspRationalComplexUnit K hζ

def sourceKPReflectionArch (b : Kˣ) : X → X :=
  sourceKPArchEuclideanAction K hζ (sourceKPRationalArchMap K hζ (sourceKPReflectionWeyl K b))

def sourceKPReflectionDifferential (b : Kˣ) (p : X) : X →L[ℝ] X :=
  ContinuousLinearMap.pi (fun v => (sourceArchReflectionDerivative ((σ b v : ℂ)⁻¹) (p v)).comp
    (ContinuousLinearMap.proj v))

theorem sourceKPReflectionArch_hasFDerivAt (b : Kˣ) (p : X) (hp : p ∈ Ω) :
    HasFDerivAt (sourceKPReflectionArch K hζ b) (sourceKPReflectionDifferential K hζ b p) p := by
  have hd : HasFDerivAt (fun q : X => fun v => sourceArchReflection ((σ b v : ℂ)⁻¹) (q v))
      (sourceKPReflectionDifferential K hζ b p) p := by
    apply hasFDerivAt_pi.mpr
    intro v
    exact HasFDerivAt.comp (f := fun q : X => q v)
      (g := sourceArchReflection ((σ b v : ℂ)⁻¹)) p
      (sourceArchReflection_hasFDerivAt _ _ (productUpper_pos hp v)) (hasFDerivAt_apply v p)
  apply hd.congr_of_eventuallyEq
  filter_upwards [(productUpper_isOpen V).mem_nhds hp] with q hq
  funext v
  exact sourceKPReflectionWeyl_euclidean K hζ b q hq v

theorem sourceKPReflectionArch_heightPoint (b : Kˣ) (y : V → ℝ) (hy : ∀ v, 0 < y v) :
    sourceKPReflectionArch K hζ b (sourceKPCuspHeightPoint K y) =
      sourceKPCuspHeightPoint K (sourceKPReflectionHeight K hζ b y) := by
  funext v
  have hp : sourceKPCuspHeightPoint K y ∈ Ω := fun v _ => hy v
  rw [sourceKPReflectionArch,sourceKPReflectionWeyl_euclidean K hζ b _ hp]
  change sourceArchReflection ((σ b v : ℂ)⁻¹) (sourceKPCuspHeightPoint K y v) = _
  rw [sourceArchReflection_vertical _ _ rfl rfl (hy v)]
  have he : Complex.normSq ((σ b v : ℂ)⁻¹) / y v = sourceKPReflectionHeight K hζ b y v := by
    rw [sourceKPReflectionHeight,Complex.normSq_eq_norm_sq,norm_inv,inv_pow,div_eq_mul_inv,mul_inv_rev]
    exact mul_comm _ _
  change WithLp.toLp 2 ![0, 0, Complex.normSq ((σ b v : ℂ)⁻¹) / y v] =
    WithLp.toLp 2 ![0, 0, sourceKPReflectionHeight K hζ b y v]
  rw [he]

private theorem pi_operator_single {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → EuclideanSpatial →L[ℝ] EuclideanSpatial) (v : ι) (w : EuclideanSpatial) :
    (ContinuousLinearMap.pi (fun k => (A k).comp (ContinuousLinearMap.proj k))) (Pi.single v w) =
      Pi.single v (A v w) := by
  funext k
  change A k ((Pi.single v w : ι → EuclideanSpatial) k) = _
  by_cases hk : k = v
  · subst k
    simp only [Pi.single_eq_same]
  · simp only [Pi.single_eq_of_ne hk,map_zero]

theorem sourceKPReflectionDifferential_single (b : Kˣ) (p : X) (v : V)
    (w : EuclideanSpatial) :
    sourceKPReflectionDifferential K hζ b p (Pi.single v w) =
      Pi.single v (sourceArchReflectionDerivative ((σ b v : ℂ)⁻¹) (p v) w) :=
  pi_operator_single (fun k => sourceArchReflectionDerivative ((σ b k : ℂ)⁻¹) (p k)) v w

theorem sourceKPReflectionDifferential_horizontal (b : Kˣ) (p : X) (hp : p ∈ Ω) (v : V)
    (h0 : p v 0 = 0) (h1 : p v 1 = 0) :
    let B := (σ b v : ℂ)⁻¹
    sourceKPReflectionDifferential K hζ b p (productDirection v 0) =
      ((p v 2)⁻¹)^2 • (-((B^2).re) • productDirection v 0 - (B^2).im • productDirection v 1) ∧
    sourceKPReflectionDifferential K hζ b p (productDirection v 1) =
      ((p v 2)⁻¹)^2 • (-((B^2).im) • productDirection v 0 + (B^2).re • productDirection v 1) := by
  dsimp only
  obtain ⟨hX,hY⟩ := sourceArchReflectionDerivative_horizontal ((σ b v : ℂ)⁻¹) (p v) h0 h1
    (productUpper_pos hp v)
  constructor
  · simp only [productDirection,sourceKPReflectionDifferential_single,hX]
    funext k
    by_cases hk : k = v
    · subst k
      simp
    · simp [Pi.single_eq_of_ne hk]
  · simp only [productDirection,sourceKPReflectionDifferential_single,hY]
    funext k
    by_cases hk : k = v
    · subst k
      simp
    · simp [Pi.single_eq_of_ne hk]

end
end ArtinMatthews
