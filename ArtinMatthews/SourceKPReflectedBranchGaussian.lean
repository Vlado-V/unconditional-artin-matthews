module

public import ArtinMatthews.SourceKPReflectedBranchData
public import ArtinMatthews.SourceKPReflectedBranchOrbit
public import ArtinMatthews.SourceKPReflectedGroupedGaussian
public import ArtinMatthews.SourceReflectionFiniteGaussianScaled
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

/-! The actual reflected branch has the literal signed Gaussian
profile and the separated arithmetic coefficient on every supported
numerator. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory QuadraticWeil VaryingKummerAnalytic
open SourcePhysical SourceReflection SourceEulerAssembly
open scoped NumberField Classical BigOperators
noncomputable section
set_option quotPrecheck false

variable (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] {ζ : K}
    (hζ : IsPrimitiveRoot ζ 12) (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
local notation "S" => sourceHilbertSet K S₀
local notation "E" => SourcePrimeExponents K S₀
local notation "PE" => SourceExteriorPrime K S₀
local notation "X" => ExteriorUnitSixthClasses S
local notation "Whole" => SWholeUnits K S
local notation "Q" => SNormOneSixthQuotient K S
local notation "N" => SNormOne K S
local notation "qmk" => sNormOneSixthQuotientMap K S
local notation "sc" => sLocalPositiveScaling K hζ S
local notation "gen" => sourcePrimeExponentUnit K hζ S₀
local notation "b[" f "," d "]" => gen (sourceReflectionActiveExponents K S₀ f+d)
local notation "I[" f "," d "]" => SourceReflectionSupportedTermIndex K S₀ f d
local notation "L" => sourceReflectionTermLength K S₀
local notation "Scale" => sourceReflectionTermScale K S₀
local notation "ω" => fun b => sourceKPReflectionProductPhase K hζ b
  (sourceKPOrientedHorizontal K hζ) (sourceKPAllInfinitePlaces K)
local notation "c" => (fun _ : InfinitePlace K => (4 : ℝ) * Real.pi)
local notation "r" => Fintype.card (InfinitePlace K)
local notation "A₀" => sourceThetaMellinScale K c
local notation "C₀[" p "]" => sourceThetaMellinConstant K S c (p).cutoff
local notation "Label[" p "]" => SourceKPReflectedRetainedLabel K hζ S₀ (p).R (p).M
local notation "ν" => sourceSLocalNormalizedSheetMeasure K hζ S
local notation "BA" => sourceKPReflectedBranchArithmetic K hζ S₀
local notation "BC" => sourceKPReflectedBranchCoefficient K hζ S₀
local notation "P" => sourceKPReflectedRetainedScaledProfile K hζ S₀
local notation "BD" => sourceKPReflectedRetainedTensor K hζ S₀
local notation "G" => sourceKPReflectedPhysicalBranchValue K hζ S₀

attribute [local instance] sourceKPReflectedRetainedLabel_fintype
local instance : Fintype X := Fintype.ofFinite _

variable {J : Ideal (𝓞 K)} {T : ℝ}

theorem sourceKPReflectedBranch_gaussian
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)
    (η : EvenIdealRayCharacter K J) (hJ : J ≠ ⊥) (hcut : principalAngularCutoff K J ⊆ S)
    (v : InfinitePlace K) (hT : 2 < T) (p : SourceKPPositiveSeedData K hζ S₀ hS hJ hT)
    (h d : E) (f : Finset PE) (hf : f ∈ sourceReflectionActiveChoices K S₀ h)
    (hd : sourceReflectionIsSquarefree d) (hdh : Disjoint d.support h.support)
    (u : X) {Z : ℝ} (hZ : 0 < Z) :
    let F := sourceKPPositivePhysicalBranchValue K hζ S₀ hS η hJ hT p (h+d) u (f∪d.support)
    let hF := sourceKPPositivePhysicalBranchValue_invariant K hζ S₀ hS η hJ hcut hT p (h+d) u (f∪d.support)
    sourceThetaGaussianProfile (C₀[p]) A₀ r 1 (sourceSLocalQuotientSheetProfile S hζ (ν v) F hF) (1/Z) =
      ∑' j : I[f,d] × (X × Label[p]),
        BA hS η hJ u j.2.1 h d f j.1.val j.2.2.2.2 *
          P hS η hJ hT p u v (some j.2.2)
            (L j.1.val.1.val j.1.val.2.1 j.1.val.2.2.val / Scale Z f d) := by
  let b := b[f,d]
  let R := (Scale Z f d)⁻¹
  let G₀ := G hS η hJ hT p (h+d) u (f∪d.support) b
  let hG₀ := sourceKPReflectedPhysicalBranchValue_invariant K hζ S₀ hS η hJ hcut hT p (h+d) u (f∪d.support) b
  let G₁ (x : Whole) := ω b * G₀ x
  have hG₁ : sourceSLocalSixthInvariant S G₁ := by
    intro x γ
    exact congrArg (fun z : ℂ => ω b*z) (hG₀ x γ)
  have hsheet : sourceSLocalQuotientSheetProfile S hζ (ν v) G₁ hG₁ =
      fun t => ω b * sourceSLocalQuotientSheetProfile S hζ (ν v) G₀ hG₀ t := by
    funext t
    unfold sourceSLocalQuotientSheetProfile
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with q
    obtain ⟨n,rfl⟩ := QuotientGroup.mk_surjective q
    change sourceSLocalQuotientSheetFunction S hζ G₁ hG₁ t (qmk n) =
      ω b * sourceSLocalQuotientSheetFunction S hζ G₀ hG₀ t (qmk n)
    rw [sourceSLocalQuotientSheetFunction_mk,sourceSLocalQuotientSheetFunction_mk]
  have hR : 0 < R := inv_pos.mpr (sourceReflectionTermScale_pos K S₀ hZ f d)
  let M := sourceKPReflectedBranchCoefficientMajorant K hζ S₀ hS hJ hT p
  let D := BD hS η hJ hT p u v
  let a (ε : X) (l : Label[p]) (i : SourceReflectionTermIndex K S₀ f) :=
    BC hS η hJ hT p u ε h d f i l
  let dil (ε : X) := sourceKPReflectedBranchDilation K hζ S₀ ε f
  have hM : 0 < M := sourceKPReflectedBranchCoefficientMajorant_pos K hζ S₀ hS hJ hT p
  have ha (ε : X) (l : Label[p]) (i : SourceReflectionTermIndex K S₀ f) :
      ‖a ε l i‖ ≤ M * sourceReflectionDirichletTerm K S₀ f 0 i :=
    sourceKPReflectedBranchCoefficient_norm_le K hζ S₀ hS η hJ hT p u ε h d f i l
  have hg := sourceReflectionGroupedGaussian_of_hasSum K hζ S₀ v f d D (C₀[p]) A₀ r
    (by norm_num : 0 ≤ (1/3 : ℝ)) (σ := 2) (by norm_num) a hM ha dil
    (fun ε _ ht => sourceKPReflectedBranchDilation_norm K hζ S₀ ε f ht) G₁ hG₁
    (fun t _ n => sourceKPReflectedBranchOrbit_hasSum K hζ S₀ hS η hJ hcut hT p h d f hf hd hdh u v t n)
    hR
  rw [hsheet, sourceThetaGaussianProfile_const_mul] at hg
  calc
    _ = ω b * sourceThetaGaussianProfile (C₀[p]) A₀ r (-1)
        (sourceSLocalQuotientSheetProfile S hζ (ν v) G₀ hG₀) R :=
      sourceKPPhysicalBranch_gaussian_reflection K hζ S₀ hS η hJ hcut v hT p (h+d) u f d hZ
    _ = _ := by
      rw [hg]
      apply tsum_congr
      intro j
      have hp := sourceKPReflectedRetainedProfile_eq_weightedSheet K hζ S₀ hS η hJ hT p u v j.2.2
      change a j.2.1 j.2.2 j.1.val * (sourceThetaGaussianProfile (C₀[p]) A₀ r (-1)
        ((D j.2.2).weightedSheet 0 (fun _ => 1))) _ = _
      rw [← hp]
      unfold sourceKPReflectedRetainedScaledProfile sourceReflectionOptionProfile
      dsimp only [a, R]
      rw [sourceKPReflectedBranchCoefficient,div_eq_mul_inv,mul_assoc]
      rfl

end
end ArtinMatthews
