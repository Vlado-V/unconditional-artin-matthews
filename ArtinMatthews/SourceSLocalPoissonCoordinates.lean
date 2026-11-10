module

public import ArtinMatthews.SourceSLocalAdditiveProbeBinding
public import ArtinMatthews.SourceComplexSchwartzDilate
public import ArtinMatthews.SourceSIntegerAnnularTerms
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

/-! Exact completion coordinates for the literal source test and its
dual, with the source norm equal to the product of the Jacobians. -/
namespace ArtinMatthews.SourcePhysical

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion IsDedekindDomain
open VaryingKummerAnalytic
open scoped NumberField Classical BigOperators SchwartzMap
noncomputable section
variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "CPlaces" => {v : InfinitePlace K // IsComplex v}

def sourceSLocalArchComplexUnits (t : SWholeUnits K S) (w : CPlaces) : ℂˣ :=
  Units.map (ringEquivComplexOfIsComplex w.property).toMonoidHom (t.1 w.val)

theorem sourceSLocalArchComplexUnits_norm (t : SWholeUnits K S) (w : CPlaces) :
    ‖(sourceSLocalArchComplexUnits K S t w : ℂ)‖ = ‖(t.1 w.val : w.val.Completion)‖ :=
  (isometry_extensionEmbedding w.val).norm_map_of_map_zero (map_zero _) _

theorem sourceSLocalArchComplexUnits_inv (t : SWholeUnits K S) (w : CPlaces) :
    sourceSLocalArchComplexUnits K S t⁻¹ w = (sourceSLocalArchComplexUnits K S t w)⁻¹ := by
  change Units.map (ringEquivComplexOfIsComplex w.property).toMonoidHom (t.1 w.val)⁻¹ = _
  exact map_inv _ _

def sourceSLocalDilationSchwartz (t : SWholeUnits K S) (w : CPlaces) : 𝓢(ℂ, ℂ) :=
  sourceComplexSchwartzDivDilate (sourceSLocalArchComplexUnits K S t w) sourceAnnularSchwartzTest

variable [IsTotallyComplex K]

theorem sourceSLocalCompletionRingEquiv_diagonal (x : K) :
    sourceSLocalCompletionRingEquiv K S (sLocalRingDiagonal K S x) =
      (sourceComplexFieldEmbedding K x, sourceFiniteFieldEmbedding K S x) := by
  apply Prod.ext
  · funext w
    change extensionEmbedding w.val (algebraMap K w.val.Completion x) = w.val.embedding x
    change extensionEmbedding w.val (((WithAbs.equiv w.val.1).symm x : WithAbs w.val.1) : w.val.Completion) = _
    rw [extensionEmbedding_coe, RingEquiv.apply_symm_apply]
  · rfl

theorem sourceSLocalCompletionRingEquiv_unit (t : SWholeUnits K S) :
    sourceSLocalCompletionRingEquiv K S (sourceSLocalUnitAdditivePoint K S t) =
      (fun w : CPlaces => (sourceSLocalArchComplexUnits K S t w : ℂ),
       fun v : S => (t.2 v : v.val.adicCompletion K)) := rfl

theorem sourceSLocalDilationProbe_eq_tensor (t : SWholeUnits K S) (x : K) :
    sourceSLocalCompletionProbe K S
      (sLocalRingDiagonal K S x * sourceSLocalUnitAdditivePoint K S t⁻¹) =
      sourceComplexTensor (sourceSLocalDilationSchwartz K S t) (sourceComplexFieldEmbedding K x) *
        sourceFiniteUnitTest K S (sourceFiniteDilationPoint K S t.2 x) := by
  rw [sourceSLocalCompletionProbe_eq_coordinate, map_mul, sourceSLocalCompletionRingEquiv_diagonal,
    sourceSLocalCompletionRingEquiv_unit]
  unfold sourceSLocalAdditiveProbe
  congr 1
  · unfold sourceComplexProductTest sourceComplexTensor sourceSLocalDilationSchwartz
    apply Finset.prod_congr rfl
    intro w _
    change sourceAnnularSchwartzTest
      (sourceComplexFieldEmbedding K x w * (sourceSLocalArchComplexUnits K S t⁻¹ w : ℂ)) = _
    rw [sourceComplexSchwartzDivDilate_apply, sourceSLocalArchComplexUnits_inv,
      Units.val_inv_eq_inv_val, div_eq_mul_inv]
  · congr 1
    funext v
    change algebraMap K (v.val.adicCompletion K) x * (((t.2 v)⁻¹ : (v.val.adicCompletion K)ˣ) :
      v.val.adicCompletion K) = algebraMap K (v.val.adicCompletion K) x / (t.2 v : v.val.adicCompletion K)
    rw [Units.val_inv_eq_inv_val, div_eq_mul_inv]

theorem sourceSLocalDilationDual_eq_tensor (t : SWholeUnits K S) (x : K) :
    sourceSLocalCompletionFourier K S (sourceSLocalCompletionProbe K S)
      (sourceSLocalUnitAdditivePoint K S t * sLocalRingDiagonal K S x) =
      sourceNumberFieldComplexFourier K sourceComplexProductTest
        (fun w => (sourceSLocalArchComplexUnits K S t w : ℂ) * sourceComplexFieldEmbedding K x w) *
      sourceFiniteLocalFourier K S (sourceFiniteUnitTest K S)
        (sourceFiniteDilationMul K S t.2 (sourceFiniteFieldEmbedding K S x)) := by
  rw [sourceSLocalCompletionProbe_fourier_eq_coordinate, map_mul,
    sourceSLocalCompletionRingEquiv_diagonal, sourceSLocalCompletionRingEquiv_unit]
  exact sourceSLocalAdditiveFourier_prod K S sourceComplexProductTest (sourceFiniteUnitTest K S) _

theorem sourceSLocalDilationJacobian (t : SWholeUnits K S) :
    (∏ w : CPlaces, ‖(sourceSLocalArchComplexUnits K S t w : ℂ)‖ ^ 2) *
      sourceFiniteDilationNorm K S t.2 = sLocalNorm K S t := by
  rw [sLocalNorm_eq_prod, sourceFiniteDilationNorm]
  congr 1
  simp only [sourceSLocalArchComplexUnits_norm]
  let e : InfinitePlace K ≃ CPlaces :=
    ⟨fun w => ⟨w, IsTotallyComplex.isComplex w⟩, Subtype.val, fun _ => rfl, fun _ => rfl⟩
  calc
    _ = ∏ w : InfinitePlace K, ‖(t.1 w : w.Completion)‖ ^ (2 : ℕ) :=
      (e.prod_comp (fun w : CPlaces => ‖(t.1 w.val : w.val.Completion)‖ ^ (2 : ℕ))).symm
    _ = _ := Finset.prod_congr rfl (fun w _ => by
      rw [InfinitePlace.mult_isComplex ⟨w, IsTotallyComplex.isComplex w⟩])

end
end ArtinMatthews.SourcePhysical
