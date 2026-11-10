module

public import ArtinMatthews.SourceThetaArchMellin
public import ArtinMatthews.SourceThetaFiniteMellin
public import ArtinMatthews.SourceThetaMellinConstants
public import ArtinMatthews.SourceThetaGaussianSmoothing
public import ArtinMatthews.SourceSLocalSheetMellin
public import ArtinMatthews.SourceSLocalProbeSheetIdentity
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
public import Mathlib.RingTheory.WittVector.IsPoly
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

/-! The literal source03 positive profile on the exact normalized
norm-one Haar sheet, with the positive Mellin constants determined
by its actual local factors. -/
namespace ArtinMatthews.SourceReflection

open NumberField NumberField.InfinitePlace IsDedekindDomain MeasureTheory Set
open ArtinMatthews.SourcePhysical ArtinMatthews.VaryingKummerAnalytic
open scoped NumberField Classical ArtinMatthews.SourcePhysical
noncomputable section

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (c : InfinitePlace K → ℝ)
variable (U : ∀ p : S, SourceThetaFiniteCutoff K p.val)

def sourceThetaPositiveTensor (x : SWholeUnits K S) : ℂ :=
  (∏ w, sourceThetaArchFactor K w (c w) (x.1 w)) * ∏ p, (U p).factor (x.2 p)

def sourceThetaMellinConstant : ℝ :=
  (∏ w, sourceThetaArchConstant (c w)) * ∏ p, (U p).mass

def sourceThetaMellinScale : ℝ :=
  ∏ w, sourceThetaArchScale (c w)

theorem sourceThetaMellinConstant_pos (hc : ∀ w, 0 < c w) :
    0 < sourceThetaMellinConstant K S c U := by
  exact mul_pos (Finset.prod_pos fun w _ => sourceThetaArchConstant_pos (hc w))
    (Finset.prod_pos fun p _ => (U p).mass_pos)

theorem sourceThetaMellinScale_pos (hc : ∀ w, 0 < c w) : 0 < sourceThetaMellinScale K c :=
  Finset.prod_pos fun w _ => sourceThetaArchScale_pos (hc w)

variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (v : InfinitePlace K)

local notation "hv" => sourceSLocalComplexPlace K hζ v
local notation "μAll" => sourceSLocalUnitProductMeasure K hζ S
local notation "ν" => sourceSLocalNormalizedSheetMeasure K hζ S v

def sourceThetaPositiveSheet : ℝ → ℂ :=
  sourceSLocalSheetProfile S ν hζ (sourceThetaPositiveTensor K S c U)

include hζ in
private theorem sourceThetaPositiveMellinIntegrand_eq_product (s : ℂ) (x : SWholeUnits K S) :
    sourceThetaPositiveTensor K S c U x * (sLocalNorm K S x : ℂ) ^ s =
      (∏ w, sourceThetaArchMellinIntegrand K w (c w) s (x.1 w)) * ∏ p, (U p).factor (x.2 p) := by
  let A (w : InfinitePlace K) := sourceSheetArchNorm w (x.1 w)
  let B (p : S) := ‖(x.2 p : p.val.adicCompletion K)‖
  have hA (w : InfinitePlace K) : 0 ≤ A w := (sourceSheetArchNorm_pos w (x.1 w)).le
  have hB (p : S) : 0 ≤ B p := norm_nonneg _
  have hn : sLocalNorm K S x = (∏ w, A w) * ∏ p, B p := by
    rw [sLocalNorm_eq_prod]
    congr 1
    apply Finset.prod_congr rfl
    intro w _
    rw [(sourceSLocalComplexPlace K hζ w).mult_eq_two]
    rfl
  rw [hn, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg
    (Finset.prod_nonneg fun w _ => hA w) (Finset.prod_nonneg fun p _ => hB p),
    sourceThetaFinsetProd_cpow _ A s (fun w _ => hA w),
    sourceThetaFinsetProd_cpow _ B s (fun p _ => hB p), sourceThetaPositiveTensor]
  simp only [sourceThetaArchMellinIntegrand, A]
  have hF : (∏ p, (U p).factor (x.2 p)) * (∏ p, (B p : ℂ) ^ s) =
      ∏ p, (U p).factor (x.2 p) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun p _ => (U p).factor_normWeight s (x.2 p)
  rw [mul_mul_mul_comm, ← Finset.prod_mul_distrib, hF]

theorem sourceThetaPositiveWeighted_integrable (hc : ∀ w, 0 < c w) (s : ℂ)
    (hs : -(5 / 6 : ℝ) < s.re) :
    Integrable (fun x => sourceThetaPositiveTensor K S c U x * (sLocalNorm K S x : ℂ) ^ s) μAll := by
  have hA := Integrable.fintype_prod_dep (μ := sourceSLocalArchUnitMeasure K hζ)
    (f := fun w => sourceThetaArchMellinIntegrand K w (c w) s)
    (fun w => sourceThetaArchMellinIntegrand_integrable K hζ w (hc w) s hs)
  have hF := Integrable.fintype_prod_dep (μ := sourceSLocalFiniteUnitMeasure K S)
    (f := fun p => (U p).factor) (fun p => (U p).factor_integrable)
  exact (hA.mul_prod hF).congr (Filter.Eventually.of_forall fun x =>
    (sourceThetaPositiveMellinIntegrand_eq_product K S c U hζ s x).symm)

theorem sourceThetaPositiveWeighted_integral (hc : ∀ w, 0 < c w) (s : ℂ)
    (hs : -(5 / 6 : ℝ) < s.re) :
    (∫ x, sourceThetaPositiveTensor K S c U x * (sLocalNorm K S x : ℂ) ^ s ∂μAll) =
      sourceThetaMellinSymbol (sourceThetaMellinConstant K S c U) (sourceThetaMellinScale K c)
        (Fintype.card (InfinitePlace K)) s := by
  let A (x : ∀ w : InfinitePlace K, w.Completionˣ) :=
    ∏ w, sourceThetaArchMellinIntegrand K w (c w) s (x w)
  let B (x : ∀ p : S, (p.val.adicCompletion K)ˣ) := ∏ p, (U p).factor (x p)
  have ha : (∫ x, A x ∂Measure.pi (sourceSLocalArchUnitMeasure K hζ)) =
      ∏ w, (sourceThetaArchConstant (c w) : ℂ) * (sourceThetaArchScale (c w) : ℂ) ^ s *
        (Complex.Gamma (s + 5 / 6) * Complex.Gamma (s + 7 / 6)) := by
    unfold A
    rw [integral_fintype_prod_eq_prod]
    exact Finset.prod_congr rfl fun w _ =>
      (sourceThetaArchMellinIntegrand_integral K hζ w (hc w) s hs).trans
        (sourceThetaArchMellin_factor (hc w) s)
  have hb : (∫ x, B x ∂Measure.pi (sourceSLocalFiniteUnitMeasure K S)) =
      ∏ p, ((U p).mass : ℂ) := by
    unfold B
    rw [integral_fintype_prod_eq_prod]
    exact Finset.prod_congr rfl fun p _ => (U p).factor_integral
  calc
    _ = ∫ x : SWholeUnits K S, A x.1 * B x.2 ∂μAll :=
      integral_congr_ae (Filter.Eventually.of_forall
        (sourceThetaPositiveMellinIntegrand_eq_product K S c U hζ s))
    _ = _ := by
      rw [sourceSLocalUnitProductMeasure, integral_prod_mul A B, ha, hb, sourceThetaMellinSymbol,
        sourceThetaMellinConstant, sourceThetaMellinScale, Complex.ofReal_mul,
        sourceThetaFinsetProd_cpow _ _ s (fun w _ => (sourceThetaArchScale_pos (hc w)).le)]
      simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Complex.ofReal_prod, mul_pow]
      ac_rfl

/-- The Mellin transform of the genuine positive theta sheet on its full convergence half-plane. -/
theorem sourceThetaPositiveSheet_hasMellin (hc : ∀ w, 0 < c w) (s : ℂ)
    (hs : -(5 / 6 : ℝ) < s.re) :
    HasMellin (sourceThetaPositiveSheet K S c U hζ v) s
      (sourceThetaMellinSymbol (sourceThetaMellinConstant K S c U) (sourceThetaMellinScale K c)
        (Fintype.card (InfinitePlace K)) s) := by
  have : BorelSpace (SWholeUnits K S) := sourceSWholeUnits_product_borel S v
  have : Measure.IsHaarMeasure ν := sourceSLocalNormalizedSheetMeasure_isHaar K hζ S v
  have : SigmaFinite ν := sourceSLocalNormalizedSheetMeasure_sigmaFinite K hζ S v
  have hI : Integrable (fun x => sourceThetaPositiveTensor K S c U x * (sLocalNorm K S x : ℂ) ^ s)
      (sourceSLocalRadialHaar S hv ν) := by
    rw [← sourceSLocalUnitProductMeasure_eq_radial K hζ S v]
    exact sourceThetaPositiveWeighted_integrable K S c U hζ hc s hs
  have h := sourceSLocalSheetProfile_hasMellin S hv ν hζ (sourceThetaPositiveTensor K S c U) s hI
  unfold sourceSLocalRadialMellin at h
  rw [← sourceSLocalUnitProductMeasure_eq_radial K hζ S v,
    sourceThetaPositiveWeighted_integral K S c U hζ hc s hs] at h
  exact h

/-- The actual positive sheet smooths to the exact Gaussian weight in the reflected coefficient. -/
theorem sourceThetaPositiveSheet_smoothing (hc : ∀ w, 0 < c w) {u : ℝ} (hu : 0 < u) :
    sourceThetaGaussianSmoothing (sourceThetaMellinConstant K S c U) (sourceThetaMellinScale K c)
      (Fintype.card (InfinitePlace K)) (sourceThetaPositiveSheet K S c U hζ v) u =
      (reflectionGaussian u : ℂ) :=
  sourceThetaGaussianSmoothing_eq_reflectionGaussian (sourceThetaMellinConstant_pos K S c U hc)
    (sourceThetaMellinScale_pos K c hc) _ _
    (sourceThetaPositiveSheet_hasMellin K S c U hζ v hc 0 (by norm_num)).1
    (fun t => (sourceThetaPositiveSheet_hasMellin K S c U hζ v hc _ (by simp)).2) hu

end
end ArtinMatthews.SourceReflection
