module

public import ArtinMatthews.SourceKPCuspRationalHeight
public import ArtinMatthews.SourceKPCompactC2Core
public import ArtinMatthews.SourceArchMobiusCoordinates
public import ArtinMatthews.SourceKPCompactRationalTransport
public import ArtinMatthews.SourceKPCompactTruncatedChart
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

/-! Signed rational Weyl coordinates on the actual compact quotient.
The finite lift and the full tuple of archimedean heights are retained. -/
namespace ArtinMatthews
open NumberField Matrix Matrix.GeneralLinearGroup SourceArchJacquet
open SourceHyperbolicGreen OAI.CubicEisenstein
open scoped NumberField MatrixGroups AdeleRing Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPReflectionWeylSL (b : Kˣ) : SL(2,K) :=
  ⟨!![0, -((b : K)⁻¹); (b : K), 0], by simp [Matrix.det_fin_two, b.ne_zero]⟩

def sourceKPReflectionWeyl (b : Kˣ) : PGL(2,K) :=
  ProjGenLinGroup.mk (sourceKPReflectionWeylSL K b : GL (Fin 2) K)

theorem sourceKPReflectionWeyl_eq (b : Kˣ) :
    sourceKPReflectionWeyl K b =
      sourceKPProjectiveDiagonalHom K ((b⁻¹)^2) * sourceKPProjectiveDiagonalHom K (-1) *
        ProjGenLinGroup.mk (sourceKPWeylMatrix K) := by
  have he : (sourceKPReflectionWeylSL K b : GL (Fin 2) K) =
      (sourceKPDiagonalHom K ((b⁻¹)^2) * sourceKPDiagonalHom K (-1) *
        sourceKPWeylMatrix K) * GeneralLinearGroup.scalar (Fin 2) b := by
    apply GeneralLinearGroup.ext
    intro i j
    rw [sourceKPMatrix_right_scalar_entry]
    change (!![0, -((b : K)⁻¹); (b : K), 0] : Matrix (Fin 2) (Fin 2) K) i j =
      _ * (b : K)
    fin_cases i <;> fin_cases j <;>
      simp [sourceKPReflectionWeylSL, sourceKPDiagonalHom, sourceKPWeylMatrix,
        Matrix.mul_apply, Fin.sum_univ_two] <;>
      field_simp [b.ne_zero]
  rw [sourceKPReflectionWeyl,he,map_mul,ProjGenLinGroup.mk_scalar,mul_one,map_mul,map_mul]
  rfl

local notation "V" => InfinitePlace K
local notation "σ" => sourceKPCuspRationalComplexUnit K hζ

theorem sourceKPReflectionWeyl_arch_at (b : Kˣ) (v : V) :
    sourceKPArchProjectiveAt K hζ v
      (sourceKPRationalArchMap K hζ (sourceKPReflectionWeyl K b)) =
    ProjGenLinGroup.mk ((complexDiagonal ((σ b v : ℂ)⁻¹) (inv_ne_zero (σ b v).ne_zero) *
      complexWeyl : SL(2,ℂ)) : GL (Fin 2) ℂ) := by
  change sourceKPArchProjectiveAt K hζ v (ProjGenLinGroup.map
    (algebraMap K (InfiniteAdeleRing K))
    (ProjGenLinGroup.mk (sourceKPReflectionWeylSL K b : GL (Fin 2) K))) = _
  rw [ProjGenLinGroup.map_mk, sourceKPArchProjectiveAt_mk]
  apply congrArg ProjGenLinGroup.mk
  apply GeneralLinearGroup.ext
  intro i j
  rw [sourceKPArchMatrixComplexEquiv_apply, sourceArchGLPiEquiv_apply,
    GeneralLinearGroup.map_apply]
  let e : K →+* ℂ := (sourceKPArchComplexEquiv K hζ v).toRingHom.comp (algebraMap K v.Completion)
  change e ((!![0, -((b : K)⁻¹); (b : K), 0] : Matrix (Fin 2) (Fin 2) K) i j) =
      ((!![(σ b v : ℂ)⁻¹, 0; 0, ((σ b v : ℂ)⁻¹)⁻¹] * !![0,-1;1,0]) :
        Matrix (Fin 2) (Fin 2) ℂ) i j
  rw [show (σ b v : ℂ) = e (b : K) from rfl]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

def sourceKPReflectionHeight (b : Kˣ) (y : V → ℝ) : V → ℝ :=
  fun v => (‖(σ b v : ℂ)‖ ^ 2 * y v)⁻¹

theorem sourceKPReflectionHeight_pos (b : Kˣ) (y : V → ℝ) (hy : ∀ v, 0 < y v) (v : V) :
    0 < sourceKPReflectionHeight K hζ b y v :=
  inv_pos.mpr (mul_pos (sq_pos_of_pos (norm_pos_iff.mpr (σ b v).ne_zero)) (hy v))

theorem sourceKPReflectionWeyl_euclidean (b : Kˣ) (p : ProductSpace V)
    (hp : p ∈ productUpper V) (v : V) :
    sourceKPArchEuclideanAction K hζ
      (sourceKPRationalArchMap K hζ (sourceKPReflectionWeyl K b)) p v =
      euclideanComplexDilation ((σ b v : ℂ)⁻¹) (euclideanWeylAction (p v)) := by
  let B := (σ b v : ℂ)⁻¹
  have hb : B ≠ 0 := inv_ne_zero (σ b v).ne_zero
  have h := productUpper_pos hp v
  rw [sourceKPArchEuclideanAction_apply,sourceKPReflectionWeyl_arch_at,
    sourceArchEuclideanProjectiveAction_specialLinear _ _ h]
  change sourceArchMobiusEuclidean (complexDiagonal B hb * complexWeyl) (p v) = _
  rw [sourceArchMobiusEuclidean_mul _ _ _ h,
    sourceArchMobiusEuclidean_diagonal _ _ _ (sourceArchMobiusEuclidean_positive _ _ h),
    sourceArchMobiusEuclidean_weyl _ h]

theorem sourceKPReflectionWeyl_pullback (b : Kˣ) (qf : SourceKPFiniteLevelFiber K hζ)
    (W : SourceKPAutomorphicCompactLevel K hζ → ℂ)
    (p : ProductSpace V) (hp : p ∈ productUpper V) :
    sourceKPCompactChartPullback K hζ W qf p =
      sourceKPCompactChartPullback K hζ W (sourceKPReflectionWeyl K b • qf)
        (sourceKPArchEuclideanAction K hζ
          (sourceKPRationalArchMap K hζ (sourceKPReflectionWeyl K b)) p) := by
  let γ := sourceKPReflectionWeyl K b
  let a := sourceKPRationalArchMap K hζ γ
  have ha := sourceKPArchEuclideanAction_positive K hζ a p
  rw [sourceKPCompactChartPullback_of_positive K hζ W qf p hp,
    sourceKPCompactChartPullback_of_positive K hζ W (γ • qf) _ ha]
  unfold sourceKPArchEuclideanAction
  rw [sourceKPArchUpperEuclideanMap_left_inverse,sourceKPUpperToCompact_rational]

end
end ArtinMatthews
