module

public import ArtinMatthews.SourceKPPhysicalRowWeight
public import ArtinMatthews.SourceKPPositiveSeedPhysicalCoefficient
public import ArtinMatthews.SourceSLocalQuotientSheet
public import ArtinMatthews.SourceThetaPositiveCoefficientSeries
public import ArtinMatthews.SourceFrequencyPoissonArgument
public import ArtinMatthews.SourceKPPositiveOrbitCharacter
public import ArtinMatthews.SourceKPPositiveOrbitTwist
public import ArtinMatthews.SourceKPPositivePhysicalOrbit
public import ArtinMatthews.SourceKPPositiveQuotientSeries
public import ArtinMatthews.SourcePrimeNormSummability
public import ArtinMatthews.SourceSLocalQuotientOrbitExpansion
public import ArtinMatthews.SourceThetaPositiveSeriesSmoothing
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

/-! The forward Gaussian of the actual physical residual seed equals
the literal coefficient row on the genuine norm-one quotient. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain QuadraticWeil MeasureTheory
open AllowedGenerators VaryingKummerAnalytic SourcePhysical SourceReflection SourceEulerAssembly
open scoped NumberField Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] {ζ : K}
    (hζ : IsPrimitiveRoot ζ 12) (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
local notation "S" => sourceHilbertSet K S₀
local notation "Whole" => SWholeUnits K S
local notation "E" => SourcePrimeExponents K S₀
local notation "C" => ReflectionSquarefreeExponents K S₀
local notation "Γ" => sNormOneSixthSubgroup K S
local notation "D" => sWholeDiagonal K S
local notation "gen" => sourcePrimeExponentUnit K hζ S₀
local notation "angle" => sourceKPOrientedHorizontal K hζ
local notation "bessel" => (fun _ : InfinitePlace K => 4*Real.pi)

variable {J : Ideal (𝓞 K)}

def sourceKPPositivePhysicalRowValue
    (hS : standardWeilBadPlaces K ⊆ S) (η : EvenIdealRayCharacter K J) (hJ : J ≠ ⊥)
    {T : ℝ} (hT : 2 < T) (p : SourceKPPositiveSeedData K hζ S₀ hS hJ hT)
    (e : E) (u : ExteriorUnitSixthClasses S) (x : Whole) : ℂ :=
  sourceKPPositivePhysicalFiniteValue K hζ S₀ e p.R p.M angle (one_le_two.trans hT.le)
    (sourceKPPositiveSeedData_q₀ K hζ S₀ p) (fun _ => 1)
    (sourceKPPhysicalRowWeight K hζ S₀ hS η hJ (sourceExteriorUnitSixthRepresentative S u)) x

set_option maxRecDepth 4096 in
theorem sourceKPPositivePhysicalRowValue_hasSum
    (hS : standardWeilBadPlaces K ⊆ S) (η : EvenIdealRayCharacter K J) (hJ : J ≠ ⊥)
    (hcut : principalAngularCutoff K J ⊆ S)
    {T : ℝ} (hT : 2 < T) (p : SourceKPPositiveSeedData K hζ S₀ hS hJ hT)
    (e : E) (u : ExteriorUnitSixthClasses S) (x : Whole) :
    HasSum (fun z : (C × E) × Γ =>
      reflectionCoefficientBeforeGaussian K hζ S₀ hS η z.1.1 z.1.2
        (sourceReflectionCanonicalRow K S₀ hζ e u) *
      sourceThetaPositiveTensor K S bessel p.cutoff
        ((x * (z.2.val : Whole))*D (gen (z.1.1.val + 3 • z.1.2))))
      (sourceKPPositivePhysicalRowValue K hζ S₀ hS η hJ hT p e u x) := by
  let r := sourceExteriorUnitSixthRepresentative S u
  let a (i : C × E) := reflectionCoefficientBeforeGaussian K hζ S₀ hS η i.1 i.2
    (sourceReflectionCanonicalRow K S₀ hζ e u)
  have ha (c : C) (n : E) (γ : Γ) :
      let m := (sourceKPAllowedSquarefreeCubeFieldEquiv K hζ S₀ ((c,n),γ)).val
      (sourceKPPhysicalRowWholeCharacter K hζ S₀ hS η hJ r (D m) : ℂ) *
        sourceKPPositivePhysicalTwistScalar K hζ S₀ e (fun _ => 1) m *
        sourceKPRetainedExteriorWhittaker K hζ S₀ hS m = a (c,n) := by
    dsimp only
    rw [sourceKPPositivePhysicalTwistScalar_orbit K hζ S₀ hS e c n γ]
    have he := sourceKPPositiveOrbitArithmetic_total K hζ S₀ hS η hJ hcut e u c n γ
    dsimp only at he
    simpa only [r,a] using he
  exact sourceKPPositivePhysicalFiniteValue_orbit K hζ S₀ hS η hJ r hT p e (fun _ => 1) a ha x

private theorem sourceKPPositiveExponents_countable : Countable E := by
  let f (e : E) := (sourcePrimeExponentNorm K S₀ e : ℝ) ^ (-2 : ℝ)
  have hs : Summable f := sourcePrimeExponentNorm_summable K S₀ (σ := 2) (by norm_num)
  have h : Function.support f = Set.univ := Set.eq_univ_of_forall fun e =>
    (Real.rpow_pos_of_pos (Nat.cast_pos.mpr (sourcePrimeExponentNorm_pos K S₀ e)) _).ne'
  exact Set.countable_univ_iff.mp (h ▸ hs.countable_support)

theorem sourceKPPositivePhysicalRow_quotient
    (hS : standardWeilBadPlaces K ⊆ S) (η : EvenIdealRayCharacter K J) (hJ : J ≠ ⊥)
    (hcut : principalAngularCutoff K J ⊆ S) (v : InfinitePlace K)
    {T : ℝ} (hT : 2 < T) (p : SourceKPPositiveSeedData K hζ S₀ hS hJ hT)
    (e : E) (u : ExteriorUnitSixthClasses S) :
    let F := sourceKPPositivePhysicalRowValue K hζ S₀ hS η hJ hT p e u
    ∃ hF : sourceSLocalSixthInvariant S F, ∀ t : ℝ, 0 < t →
      sourceSLocalQuotientSheetProfile S hζ (sourceSLocalNormalizedSheetMeasure K hζ S v) F hF t =
        sourceThetaPositiveCoefficientSeries K hζ S₀ hS η S bessel p.cutoff v
          (sourceReflectionCanonicalRow K S₀ hζ e u) t := by
  let _ : Countable E := sourceKPPositiveExponents_countable K S₀
  let _ : Countable C := by unfold ReflectionSquarefreeExponents; infer_instance
  let F := sourceKPPositivePhysicalRowValue K hζ S₀ hS η hJ hT p e u
  let row := sourceReflectionCanonicalRow K S₀ hζ e u
  let A (i : C × E) := reflectionCoefficientBeforeGaussian K hζ S₀ hS η i.1 i.2 row
  let d (i : C × E) := D (gen (i.1.val + 3 • i.2))
  let H := sourceThetaPositiveSheet K S bessel p.cutoff hζ v
  let B := sourceThetaPositiveTensor K S bessel p.cutoff
  have hc (w : InfinitePlace K) : 0 < bessel w := mul_pos (by norm_num) Real.pi_pos
  have h (x : Whole) : HasSum (fun i : (C × E) × Γ =>
      A i.1 * B ((x * (i.2.val : Whole))*d i.1)) (F x) :=
    sourceKPPositivePhysicalRowValue_hasSum K hζ S₀ hS η hJ hcut hT p e u x
  have hF := sourceSLocalSixthInvariant_of_orbit_hasSum S F
    (fun i x => A i * B (x*d i)) h
  refine ⟨hF,fun t ht => ?_⟩
  have hd (i : C × E) : sLocalNorm K S (d i) = sourcePrimeExponentNorm K S₀ (i.1.val + 3 • i.2) :=
    sourcePrimeExponentUnit_fieldSNorm K hζ S₀ (i.1.val + 3 • i.2)
  have hA : Summable (fun i => ‖A i‖ * sLocalNorm K S (d i)^(-2:ℝ)) := by
    simp_rw [hd]
    exact reflectionCoefficientBeforeGaussian_dirichlet_summable K hζ S₀ hS η row (by norm_num)
  have hu := (sourceKPPositiveQuotientSeries_unfold K S hζ v bessel hc p.cutoff A d F hF h hA ht).2
  rw [hu,sourceThetaPositiveCoefficientSeries_eq_product_tsum K hζ S₀ hS η S bessel p.cutoff v hc row ht]
  apply tsum_congr
  intro i
  change A i * H (t*sLocalNorm K S (d i)) = A i * H (_*t)
  rw [hd,mul_comm t]

theorem sourceKPPositivePhysicalRow_gaussian
    (hS : standardWeilBadPlaces K ⊆ S) (η : EvenIdealRayCharacter K J) (hJ : J ≠ ⊥)
    (hcut : principalAngularCutoff K J ⊆ S) (v : InfinitePlace K)
    {T : ℝ} (hT : 2 < T) (p : SourceKPPositiveSeedData K hζ S₀ hS hJ hT)
    (e : E) (u : ExteriorUnitSixthClasses S) :
    let F := sourceKPPositivePhysicalRowValue K hζ S₀ hS η hJ hT p e u
    ∃ hF : sourceSLocalSixthInvariant S F, ∀ (Z : ℝ), 0 < Z →
      sourceThetaGaussianSmoothing (sourceThetaMellinConstant K S bessel p.cutoff)
        (sourceThetaMellinScale K bessel) (Fintype.card (InfinitePlace K))
        (sourceSLocalQuotientSheetProfile S hζ (sourceSLocalNormalizedSheetMeasure K hζ S v) F hF)
        (1/Z) =
      reflectionCoefficientRow K hζ S₀ hS η (sourceReflectionCanonicalRow K S₀ hζ e u) Z := by
  let F := sourceKPPositivePhysicalRowValue K hζ S₀ hS η hJ hT p e u
  obtain ⟨hF,h⟩ := sourceKPPositivePhysicalRow_quotient K hζ S₀ hS η hJ hcut v hT p e u
  refine ⟨hF,fun Z hZ => ?_⟩
  have hc (w : InfinitePlace K) : 0 < bessel w := mul_pos (by norm_num) Real.pi_pos
  rw [← sourceThetaPositiveCoefficientSeries_smoothing K S₀ hζ hS η S bessel hc p.cutoff v
    (sourceReflectionCanonicalRow K S₀ hζ e u) hZ]
  unfold sourceThetaGaussianSmoothing mellin
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  rw [h _ (mul_pos (one_div_pos.mpr hZ) ht)]

end
end ArtinMatthews
