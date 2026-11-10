module

public import ArtinMatthews.SourceKPTranslateCompactHaar
public import ArtinMatthews.L2MeasurableCutoff
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

/-! Actual Haar L² pullback of the finite right translates to their common level. -/
namespace ArtinMatthews
open NumberField Matrix MeasureTheory Filter
open scoped NumberField MatrixGroups AdeleRing ENNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "D" => sourceKPFiniteLevelConjugate K hζ
local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "μY" => sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)

variable (T : Finset (SourceKPFiniteAdeleProjective K hζ))
include T

local notation "J" => sourceKPFiniteTranslateLevel K hζ T
local notation "YJ" => SourceKPTranslateAutomorphicCompactLevel K hζ T
local notation "μJ" => sourceKPTranslateCompactHaar K hζ T
local notation "LY" => Lp ℂ 2 μY
local notation "LJ" => Lp ℂ 2 μJ

private theorem pullback_memLp (t : Gf) (h : J ≤ D t) (f : LY) :
    MemLp ((f : Y → ℂ) ∘ sourceKPTranslateAutomorphicCompactMap K hζ T t h) 2 μJ := by
  let p := sourceKPTranslateAutomorphicCompactMap K hζ T t h
  have hm : MemLp (f : Y → ℂ) 2 (Measure.map p μJ) := by
    change MemLp (f : Y → ℂ) 2 (Measure.map (sourceKPTranslateAutomorphicCompactMap K hζ T t h) μJ)
    rw [sourceKPTranslateAutomorphicCompactMap_haar]
    exact (Lp.memLp f).smul_measure (ENNReal.natCast_ne_top _)
  have hp : MeasurePreserving p μJ (Measure.map p μJ) :=
    ⟨(sourceKPTranslateAutomorphicCompactMap_continuous K hζ T t h).measurable, rfl⟩
  exact hm.comp_measurePreserving hp

private def pullbackValue (t : Gf) (h : J ≤ D t) (f : LY) : LJ :=
  (pullback_memLp K hζ T t h f).toLp
    ((f : Y → ℂ) ∘ sourceKPTranslateAutomorphicCompactMap K hζ T t h)

private theorem pullbackValue_coe (t : Gf) (h : J ≤ D t) (f : LY) :
    (pullbackValue K hζ T t h f : YJ → ℂ) =ᵐ[μJ]
      (f : Y → ℂ) ∘ sourceKPTranslateAutomorphicCompactMap K hζ T t h :=
  (pullback_memLp K hζ T t h f).coeFn_toLp

private theorem pullbackValue_norm_sq (t : Gf) (h : J ≤ D t) (f : LY) :
    ‖pullbackValue K hζ T t h f‖ ^ 2 = ((J).relIndex (D t) : ℝ) * ‖f‖ ^ 2 := by
  let p := sourceKPTranslateAutomorphicCompactMap K hζ T t h
  let d := (J).relIndex (D t)
  have hp := (sourceKPTranslateAutomorphicCompactMap_continuous K hζ T t h).measurable
  have hf : AEStronglyMeasurable (fun y : Y => ‖f y‖ ^ 2) (Measure.map p μJ) := by
    rw [sourceKPTranslateAutomorphicCompactMap_haar]
    exact ((Lp.memLp f).aestronglyMeasurable.norm.pow 2).smul_measure (d : ℝ≥0∞)
  rw [heightL2_norm_sq_integral μJ, heightL2_norm_sq_integral μY]
  calc
    _ = ∫ x, ‖f (p x)‖ ^ 2 ∂μJ := by
      apply integral_congr_ae
      filter_upwards [pullbackValue_coe K hζ T t h f] with x hx
      rw [hx, Function.comp_apply]
    _ = ∫ y, ‖f y‖ ^ 2 ∂(Measure.map p μJ) := (integral_map hp.aemeasurable hf).symm
    _ = _ := by
      rw [sourceKPTranslateAutomorphicCompactMap_haar, integral_smul_measure]
      simp only [ENNReal.toReal_natCast, smul_eq_mul]

def sourceKPTranslateCompactPullbackL2 (t : Gf) (h : J ≤ D t) : LY →L[ℂ] LJ := by
  let p := sourceKPTranslateAutomorphicCompactMap K hζ T t h
  let d := (J).relIndex (D t)
  let P := pullbackValue K hζ T t h
  let hp := sourceKPTranslateAutomorphicCompactMap_quasiMeasurePreserving K hζ T t h
  refine LinearMap.mkContinuous
    { toFun := P
      map_add' f g := by
        apply Lp.ext
        filter_upwards [pullbackValue_coe K hζ T t h (f+g), pullbackValue_coe K hζ T t h f,
          pullbackValue_coe K hζ T t h g, hp.ae_eq_comp (Lp.coeFn_add f g),
          Lp.coeFn_add (P f) (P g)] with x hfg hf hg hsrc hsum
        calc
          P (f+g) x = (f+g) (p x) := hfg
          _ = f (p x) + g (p x) := hsrc
          _ = P f x + P g x := congrArg₂ (· + ·) hf.symm hg.symm
          _ = (P f + P g) x := hsum.symm
      map_smul' c f := by
        apply Lp.ext
        filter_upwards [pullbackValue_coe K hζ T t h (c • f), pullbackValue_coe K hζ T t h f,
          hp.ae_eq_comp (Lp.coeFn_smul c f), Lp.coeFn_smul c (P f)] with x hcf hf hsrc hsmul
        calc
          P (c • f) x = (c • f) (p x) := hcf
          _ = c • f (p x) := hsrc
          _ = c • P f x := congrArg (c • ·) hf.symm
          _ = (c • P f) x := hsmul.symm }
    (Real.sqrt (d : ℝ)) (fun f => ?_)
  change ‖P f‖ ≤ Real.sqrt (d : ℝ) * ‖f‖
  apply (sq_le_sq₀ (norm_nonneg (P f)) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg f))).mp
  rw [pullbackValue_norm_sq K hζ T t h f, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]

theorem sourceKPTranslateCompactPullbackL2_coe (t : Gf) (h : J ≤ D t) (f : LY) :
    (sourceKPTranslateCompactPullbackL2 K hζ T t h f : YJ → ℂ) =ᵐ[μJ]
      (f : Y → ℂ) ∘ sourceKPTranslateAutomorphicCompactMap K hζ T t h :=
  pullbackValue_coe K hζ T t h f

theorem sourceKPTranslateCompactPullbackL2_norm_sq (t : Gf) (h : J ≤ D t) (f : LY) :
    ‖sourceKPTranslateCompactPullbackL2 K hζ T t h f‖ ^ 2 = ((J).relIndex (D t) : ℝ) * ‖f‖ ^ 2 :=
  pullbackValue_norm_sq K hζ T t h f

end
end ArtinMatthews
