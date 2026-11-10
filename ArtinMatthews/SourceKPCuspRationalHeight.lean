module

public import ArtinMatthews.SourceKPCuspNativeUpperPoint
public import ArtinMatthews.SourceArchOnlyCompact
public import ArtinMatthews.SourceArchGramNormalForm
public import ArtinMatthews.SourceKubotaGL2Generation
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

/-! A rational diagonal changes each positive height by the absolute value
of its complex embedding. Its remaining phase is an explicit archimedean
deep-compact factor with finite component one. -/
namespace ArtinMatthews
open NumberField Matrix Matrix.GeneralLinearGroup SourceArchJacquet OAI.CubicEisenstein
open scoped NumberField AdeleRing MatrixGroups
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

private def cuspArchUnit (u : InfinitePlace K → ℂˣ) : (InfiniteAdeleRing K)ˣ :=
  MulEquiv.piUnits.symm (fun v => Units.map (sourceKPArchComplexEquiv K hζ v).symm (u v))

private theorem cuspArchUnit_at (u : InfinitePlace K → ℂˣ) (v : InfinitePlace K) :
    Units.map (sourceKPArchComplexEquiv K hζ v)
      (MulEquiv.piUnits (cuspArchUnit K hζ u) v) = u v := by
  simp only [cuspArchUnit, MulEquiv.apply_symm_apply]
  apply Units.ext
  exact (sourceKPArchComplexEquiv K hζ v).apply_symm_apply _

private theorem cuspArchUnit_val (u : InfinitePlace K → ℂˣ) (v : InfinitePlace K) :
    sourceKPArchComplexEquiv K hζ v ((cuspArchUnit K hζ u : InfiniteAdeleRing K) v) =
      (u v : ℂ) :=
  congrArg (fun z : ℂˣ => (z : ℂ)) (cuspArchUnit_at K hζ u v)

private theorem cuspArchDiagonal_at (u : (InfiniteAdeleRing K)ˣ) (v : InfinitePlace K) :
    sourceKPArchMatrixComplexEquiv K hζ v
      (sourceArchGLPiEquiv K (sourceKPDiagonalHom (InfiniteAdeleRing K) u) v) =
      sourceGL2Diagonal (Units.map (sourceKPArchComplexEquiv K hζ v) (MulEquiv.piUnits u v)) := by
  apply GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [sourceKPArchMatrixComplexEquiv_apply, sourceArchGLPiEquiv_apply,
      sourceKPDiagonalHom, sourceGL2Diagonal] <;> rfl

private def cuspHeightUnit (y : InfinitePlace K → ℝ) (hy : ∀ v, 0 < y v) :
    (InfiniteAdeleRing K)ˣ :=
  cuspArchUnit K hζ (fun v => Units.mk0 (y v : ℂ) (Complex.ofReal_ne_zero.mpr (hy v).ne'))

private theorem cuspHeightUnit_at (y : InfinitePlace K → ℝ) (hy : ∀ v, 0 < y v)
    (v : InfinitePlace K) :
    Units.map (sourceKPArchComplexEquiv K hζ v) (MulEquiv.piUnits (cuspHeightUnit K hζ y hy) v) =
      Units.mk0 (y v : ℂ) (Complex.ofReal_ne_zero.mpr (hy v).ne') :=
  cuspArchUnit_at K hζ _ v

private theorem cuspHeightUnit_val (y : InfinitePlace K → ℝ) (hy : ∀ v, 0 < y v)
    (v : InfinitePlace K) :
    sourceKPArchComplexEquiv K hζ v ((cuspHeightUnit K hζ y hy : InfiniteAdeleRing K) v) =
      (y v : ℂ) :=
  congrArg (fun u : ℂˣ => (u : ℂ)) (cuspHeightUnit_at K hζ y hy v)

private theorem cuspHeightSection_diagonal (y : InfinitePlace K → ℝ) (hy : ∀ v, 0 < y v) :
    sourceKPCuspHeightSection K hζ y hy =
      sourceKPProjectiveDiagonalHom (InfiniteAdeleRing K) (cuspHeightUnit K hζ y hy) := by
  let r := cuspHeightUnit K hζ (fun v => Real.sqrt (y v)) (fun v => Real.sqrt_pos.mpr (hy v))
  have he : sourceArchUpperHalfspaceMatrix K hζ (sourceKPCuspHeightPoint K y) hy *
      GeneralLinearGroup.scalar (Fin 2) r =
        sourceKPDiagonalHom (InfiniteAdeleRing K) (cuspHeightUnit K hζ y hy) := by
    dsimp only [r]
    apply (sourceArchGLPiEquiv K).injective
    funext v
    apply (sourceKPArchMatrixComplexEquiv K hζ v).injective
    simp only [map_mul, Pi.mul_apply, sourceArchGLPiEquiv_scalar,
      sourceKPArchMatrixComplexEquiv_scalar, cuspArchDiagonal_at, cuspHeightUnit_at,
      sourceArchUpperHalfspaceMatrix, MulEquiv.apply_symm_apply]
    simp only [sourceKPCuspHeightPoint, WithLp.ofLp_toLp, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      Complex.ofReal_zero, zero_mul, zero_add]
    change (upperSection 0 (y v) (hy v) : GL (Fin 2) ℂ) *
      GeneralLinearGroup.scalar (Fin 2)
        (Units.mk0 (Real.sqrt (y v) : ℂ) (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (hy v)).ne')) =
      sourceGL2Diagonal (Units.mk0 (y v : ℂ) (Complex.ofReal_ne_zero.mpr (hy v).ne'))
    simpa only [sourceGL2Upper_zero, one_mul] using sourceArchUpperSection_scalar 0 (y v) (hy v)
  have h := congrArg (fun g : GL (Fin 2) (InfiniteAdeleRing K) => ProjGenLinGroup.mk g) he
  simpa only [sourceKPCuspHeightSection, sourceKPProjectiveDiagonalHom, MonoidHom.comp_apply,
    map_mul, ProjGenLinGroup.mk_scalar, mul_one] using h

def sourceKPCuspRationalComplexUnit (m : Kˣ) (v : InfinitePlace K) : ℂˣ :=
  Units.map (sourceKPArchComplexEquiv K hζ v) (Units.map (algebraMap K v.Completion).toMonoidHom m)

def sourceKPCuspRationalHeight (m : Kˣ) (y : InfinitePlace K → ℝ) : InfinitePlace K → ℝ :=
  fun v => ‖(sourceKPCuspRationalComplexUnit K hζ m v : ℂ)‖ * y v

theorem sourceKPCuspRationalHeight_pos (m : Kˣ) (y : InfinitePlace K → ℝ)
    (hy : ∀ v, 0 < y v) (v : InfinitePlace K) : 0 < sourceKPCuspRationalHeight K hζ m y v :=
  mul_pos (norm_pos_iff.mpr (sourceKPCuspRationalComplexUnit K hζ m v).ne_zero) (hy v)

private def cuspRationalNormUnit (m : Kˣ) : (InfiniteAdeleRing K)ˣ :=
  cuspHeightUnit K hζ (fun v => ‖(sourceKPCuspRationalComplexUnit K hζ m v : ℂ)‖)
    (fun v => norm_pos_iff.mpr (sourceKPCuspRationalComplexUnit K hζ m v).ne_zero)

def sourceKPCuspRationalPhaseUnit (m : Kˣ) : (InfiniteAdeleRing K)ˣ :=
  cuspArchUnit K hζ (fun v =>
    (Units.mk0 (‖(sourceKPCuspRationalComplexUnit K hζ m v : ℂ)‖ : ℂ)
      (Complex.ofReal_ne_zero.mpr
        (norm_ne_zero_iff.mpr (sourceKPCuspRationalComplexUnit K hζ m v).ne_zero)))⁻¹ *
      sourceKPCuspRationalComplexUnit K hζ m v)

private theorem cuspRationalUnit_at (m : Kˣ) (v : InfinitePlace K) :
    Units.map (sourceKPArchComplexEquiv K hζ v)
      (MulEquiv.piUnits (Units.map (algebraMap K (InfiniteAdeleRing K)).toMonoidHom m) v) =
      sourceKPCuspRationalComplexUnit K hζ m v := by
  apply Units.ext
  rfl

theorem sourceKPCuspRationalPhaseUnit_norm (m : Kˣ) (v : InfinitePlace K) :
    ‖((Units.map (sourceKPArchComplexEquiv K hζ v)
      (MulEquiv.piUnits (sourceKPCuspRationalPhaseUnit K hζ m) v) : ℂˣ) : ℂ)‖ = 1 := by
  rw [sourceKPCuspRationalPhaseUnit, cuspArchUnit_at]
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, norm_mul, norm_inv]
  rw [Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr (sourceKPCuspRationalComplexUnit K hζ m v).ne_zero)]

private theorem cuspRationalPhase_factor (m : Kˣ) :
    cuspRationalNormUnit K hζ m * sourceKPCuspRationalPhaseUnit K hζ m =
      Units.map (algebraMap K (InfiniteAdeleRing K)).toMonoidHom m := by
  apply Units.ext
  funext v
  apply (sourceKPArchComplexEquiv K hζ v).injective
  have hm : sourceKPArchComplexEquiv K hζ v
      ((Units.map (algebraMap K (InfiniteAdeleRing K)).toMonoidHom m : InfiniteAdeleRing K) v) =
        (sourceKPCuspRationalComplexUnit K hζ m v : ℂ) :=
    congrArg (fun z : ℂˣ => (z : ℂ)) (cuspRationalUnit_at K hζ m v)
  change sourceKPArchComplexEquiv K hζ v
      (((cuspRationalNormUnit K hζ m : InfiniteAdeleRing K) v) *
        ((sourceKPCuspRationalPhaseUnit K hζ m : InfiniteAdeleRing K) v)) = _
  rw [map_mul, hm]
  simp only [cuspRationalNormUnit, cuspHeightUnit_val, sourceKPCuspRationalPhaseUnit,
    cuspArchUnit_val, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
  rw [← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr
    (norm_ne_zero_iff.mpr (sourceKPCuspRationalComplexUnit K hζ m v).ne_zero)), one_mul]

def sourceKPCuspRationalPhaseCompact (m : Kˣ) : sourceKPAdelicDeepCompact K hζ :=
  sourceArchOnlyCompact K hζ
    (sourceKPDiagonalHom (InfiniteAdeleRing K) (sourceKPCuspRationalPhaseUnit K hζ m))
    (fun v => by
      rw [cuspArchDiagonal_at]
      exact ⟨sourceArchPhaseUnitary _ (sourceKPCuspRationalPhaseUnit_norm K hζ m v),
        sourceArchPhaseUnitary_coe _ _⟩)

theorem sourceKPCuspRationalPhaseCompact_val (m : Kˣ) :
    (sourceKPCuspRationalPhaseCompact K hζ m).val =
      (sourceKPProjectiveDiagonalHom (InfiniteAdeleRing K) (sourceKPCuspRationalPhaseUnit K hζ m),1) :=
  rfl

private theorem cuspRationalHeightUnit (m : Kˣ) (y : InfinitePlace K → ℝ)
    (hy : ∀ v, 0 < y v) :
    cuspHeightUnit K hζ (sourceKPCuspRationalHeight K hζ m y)
      (sourceKPCuspRationalHeight_pos K hζ m y hy) =
      cuspRationalNormUnit K hζ m * cuspHeightUnit K hζ y hy := by
  apply Units.ext
  funext v
  apply (sourceKPArchComplexEquiv K hζ v).injective
  change sourceKPArchComplexEquiv K hζ v
      ((cuspHeightUnit K hζ (sourceKPCuspRationalHeight K hζ m y) _ : InfiniteAdeleRing K) v) =
    sourceKPArchComplexEquiv K hζ v
      (((cuspRationalNormUnit K hζ m : InfiniteAdeleRing K) v) *
        ((cuspHeightUnit K hζ y hy : InfiniteAdeleRing K) v))
  simp only [cuspRationalNormUnit, map_mul, cuspHeightUnit_val,
    sourceKPCuspRationalHeight, Complex.ofReal_mul]

theorem sourceKPCuspRationalHeight_factor (m : Kˣ) (y : InfinitePlace K → ℝ)
    (hy : ∀ v, 0 < y v) (qf : SourceKPFiniteAdeleProjective K hζ) :
    sourceKPAdelicProjectiveRationalLift K hζ (sourceKPProjectiveDiagonalHom K m) *
      (sourceKPCuspHeightSection K hζ y hy,qf) =
      (sourceKPCuspHeightSection K hζ (sourceKPCuspRationalHeight K hζ m y)
          (sourceKPCuspRationalHeight_pos K hζ m y hy),
        (sourceKPAdelicProjectiveRationalLift K hζ (sourceKPProjectiveDiagonalHom K m)).2 * qf) *
        (sourceKPCuspRationalPhaseCompact K hζ m).val := by
  apply Prod.ext
  · rw [sourceKPCuspRationalPhaseCompact_val]
    change ProjGenLinGroup.map (algebraMap K (InfiniteAdeleRing K))
        (sourceKPProjectiveDiagonalHom K m) * sourceKPCuspHeightSection K hζ y hy =
      sourceKPCuspHeightSection K hζ (sourceKPCuspRationalHeight K hζ m y)
        (sourceKPCuspRationalHeight_pos K hζ m y hy) *
          sourceKPProjectiveDiagonalHom (InfiniteAdeleRing K) (sourceKPCuspRationalPhaseUnit K hζ m)
    rw [sourceKPProjectiveDiagonalHom_map,
      cuspHeightSection_diagonal, cuspHeightSection_diagonal,
      ← map_mul, ← map_mul]
    congr 1
    rw [cuspRationalHeightUnit K hζ m y hy, ← cuspRationalPhase_factor K hζ m]
    ac_rfl
  · rw [sourceKPCuspRationalPhaseCompact_val]
    change _ = _ * 1
    exact (mul_one _).symm

end
end ArtinMatthews
