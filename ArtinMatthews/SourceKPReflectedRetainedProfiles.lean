module

public import ArtinMatthews.SourceKPReflectedPhysicalTerms
public import ArtinMatthews.SourceKPRetainedThetaScaledProfiles
public import ArtinMatthews.SourceKPAdelicOutgoingRetainedReflectedTensor
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

/-! The fixed seed and the checked retained Jacquet profiles give the
literal finite tensor family used in the reflected branch. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain QuadraticWeil VaryingKummerAnalytic SourcePhysical SourceReflection
open scoped NumberField Classical BigOperators ContDiff
noncomputable section

set_option quotPrecheck false

variable (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] {ζ : K}
    (hζ : IsPrimitiveRoot ζ 12) (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
local notation "S" => sourceHilbertSet K S₀
local notation "U" => SWholeUnits K S
local notation "Q" => SLocalPowerClasses K 6 S
local notation "rep" => sourceExteriorUnitSixthRepresentative S
local notation "A" => sourceKPReflectedArchBesselFactor K S₀
local notation "L" => sourceKPLocalCompactProductLift K hζ S
local notation "C₁" => sourceKPCuspResidualFourierValue K hζ (1 : Kˣ)
local notation "r₆" => sourceKPRetainedFiniteSixthClass K S

theorem sourceKPReflectedRetained_parameter_pos : 0 < (1 / 6 : ℂ).re := by norm_num

local notation "hs" => sourceKPReflectedRetained_parameter_pos
local notation "B" => SourceKPAdelicOutgoingRetainedJacquetLabel K hζ hs S
local notation "lift" => sourceKPAdelicOutgoingRetainedJacquetBasisLift K hζ
local notation "F" => sourceKPAdelicOutgoingRetainedJacquetBasisDiagonalProfile K hζ

variable {J : Ideal (𝓞 K)} {T : ℝ}

abbrev SourceKPReflectedRetainedLabel
    (R M : ↥(sourceHilbertSet K S₀) → ℕ) :=
  SourceKPRetainedThetaLabel K hζ S₀ (SourceKPRetainedSeedIndex K S R M)

local notation "I[" p "]" => SourceKPRetainedSeedIndex K S (p).R (p).M
local notation "Label[" p "]" => SourceKPReflectedRetainedLabel K hζ S₀ (p).R (p).M

@[instance_reducible] def sourceKPReflectedRetainedLabel_fintype
    (R M : ↥(sourceHilbertSet K S₀) → ℕ) :
    Fintype (SourceKPReflectedRetainedLabel K hζ S₀ R M) :=
  sourceKPRetainedThetaLabel_fintype K hζ S₀ _

attribute [local instance] sourceKPReflectedRetainedLabel_fintype

local notation "pre[" p "]" => sourceKPAdelicOutgoingReflectedRetainedPrefix K hζ S₀ (p).R (p).M
local notation "q₀" => sourceKPPositiveSeedData_q₀ K hζ S₀

def sourceKPReflectedRetainedSeedScalar
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀) (hJ : J ≠ ⊥)
    (hT : 2 < T) (p : SourceKPPositiveSeedData K hζ S₀ hS hJ hT) (k : I[p] × B) : ℂ :=
  (C₁ (one_le_two.trans hT.le) (q₀ p))⁻¹ *
    (sourceKPRetainedSeedWeight K S p.R p.M k.1 *
      C₁ (one_le_two.trans hT.le) ((L (fun P => lift P.val hs (k.2 P))).2))

def sourceKPReflectedRetainedTensor
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)
    (η : EvenIdealRayCharacter K J) (hJ : J ≠ ⊥)
    (hT : 2 < T) (p : SourceKPPositiveSeedData K hζ S₀ hS hJ hT)
    (u : ExteriorUnitSixthClasses S) (v : InfinitePlace K)
    (l : Label[p]) : SourceThetaRotatedTensor K S hζ v (1 / 3) :=
  sourceKPRetainedThetaTensor K hζ S₀ hS η hJ (fun _ : I[p] => rep u) (fun i => pre[p] i p.a) v l

local notation "D" => sourceKPReflectedRetainedTensor K hζ S₀
local notation "χ" => sourceKPPhysicalRowFiniteCharacter K hζ S₀
local notation "χ₀" => sourceKPRetainedFiniteRowCharacter K hζ S₀

def sourceKPReflectedRetainedTensorValue
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)
    (η : EvenIdealRayCharacter K J) (hJ : J ≠ ⊥)
    (hT : 2 < T) (p : SourceKPPositiveSeedData K hζ S₀ hS hJ hT)
    (u : ExteriorUnitSixthClasses S) (v : InfinitePlace K)
    (l : Label[p]) (z : U) : ℂ :=
  sourceThetaSLocalTensor K S hζ v ((D hS η hJ hT p u v l).localDeriv 0) (D hS η hJ hT p u v l).retained z

local notation "TV" => sourceKPReflectedRetainedTensorValue K hζ S₀

theorem sourceKPReflectedRetainedTensor_sum
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)
    (η : EvenIdealRayCharacter K J) (hJ : J ≠ ⊥)
    (hT : 2 < T) (p : SourceKPPositiveSeedData K hζ S₀ hS hJ hT)
    (u : ExteriorUnitSixthClasses S)
    (v : InfinitePlace K) (G : Q → ℂ) (c : I[p] × B → ℂ) (z : U) :
    G (r₆ z.2) * (χ hS η hJ (rep u) z : ℂ) * A z *
      (∑ k : I[p] × B, c k * ∏ P : S, F P.val hs (k.2 P) (pre[p] k.1 p.a P) (z.2 P)) =
      ∑ l : Label[p], c (l.1,l.2.1) * G l.2.2 * TV hS η hJ hT p u v l z := by
  let : Fintype Q := ⟨sourceKPRetainedFiniteSixthClassLabels K hζ S₀,
    mem_sourceKPRetainedFiniteSixthClassLabels K hζ S₀⟩
  have hχ : χ hS η hJ (rep u) z = χ₀ hS η hJ (rep u) z.2 := by
    rw [sourceKPPhysicalRowFiniteCharacter_apply,sourceKPRetainedFiniteRowCharacter_value]
  rw [hχ]
  simp only [Fintype.sum_prod_type,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  let V (P : S) := F P.val hs (k P) (pre[p] i p.a P)
  calc
    _ = c (i,k) * A z *
        (G (r₆ z.2) * (χ₀ hS η hJ (rep u) z.2 : ℂ) * ∏ P : S, V P (z.2 P)) := by
          dsimp only [V]
          ring
    _ = c (i,k) * A z *
        ∑ r : Q, G r * ∏ P : S, sourceKPRetainedLocalClassProfile K P.val
          (sourceKPRetainedFiniteCharacterAt K S (χ₀ hS η hJ (rep u)) P) (r P) (V P) (z.2 P) := by
            rw [sourceKPRetainedFiniteClassTensor K hζ S₀ G (χ₀ hS η hJ (rep u)) V z.2]
            rfl
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      unfold sourceKPReflectedRetainedTensorValue sourceKPReflectedRetainedTensor
      rw [sourceKPRetainedThetaTensor_literal]
      change c (i,k) * A z * (G r * _) = c (i,k) * G r * (A z * _)
      simp only [sourceKPRetainedThetaFiniteFactor, V]
      ring

def sourceKPReflectedRetainedProfile
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)
    (η : EvenIdealRayCharacter K J) (hJ : J ≠ ⊥)
    (hT : 2 < T) (p : SourceKPPositiveSeedData K hζ S₀ hS hJ hT)
    (u : ExteriorUnitSixthClasses S) (v : InfinitePlace K)
    (l : Label[p]) : ℝ → ℂ :=
  sourceKPRetainedThetaProfile K hζ S₀ hS η hJ (fun _ : I[p] => rep u) (fun i => pre[p] i p.a) v p.cutoff l

local notation "P₀" => sourceKPReflectedRetainedProfile K hζ S₀
local notation "c" => (fun _ : InfinitePlace K => (4 : ℝ) * Real.pi)
local notation "C₀[" p "]" => sourceThetaMellinConstant K S c (p).cutoff
local notation "A₀" => sourceThetaMellinScale K c
local notation "r" => Fintype.card (InfinitePlace K)

theorem sourceKPReflectedRetainedProfile_eq_weightedSheet
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)
    (η : EvenIdealRayCharacter K J) (hJ : J ≠ ⊥)
    (hT : 2 < T) (p : SourceKPPositiveSeedData K hζ S₀ hS hJ hT)
    (u : ExteriorUnitSixthClasses S) (v : InfinitePlace K) (l : Label[p]) :
    P₀ hS η hJ hT p u v l = sourceThetaGaussianProfile (C₀[p]) A₀ r (-1) ((D hS η hJ hT p u v l).weightedSheet 0 (fun _ => 1)) :=
  sourceKPRetainedThetaProfile_eq_weightedSheet K hζ S₀ hS η hJ (fun _ : I[p] => rep u) (fun i => pre[p] i p.a) v p.cutoff l

def sourceKPReflectedRetainedScaledProfile
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)
    (η : EvenIdealRayCharacter K J) (hJ : J ≠ ⊥)
    (hT : 2 < T) (p : SourceKPPositiveSeedData K hζ S₀ hS hJ hT)
    (u : ExteriorUnitSixthClasses S) (v : InfinitePlace K)
    (l : Option Label[p]) (t : ℝ) : ℂ :=
  sourceReflectionOptionProfile (fun l t =>
    sourceKPReflectedRetainedSeedScalar K hζ S₀ hS hJ hT p (l.1,l.2.1) * P₀ hS η hJ hT p u v l t) l t

theorem sourceKPReflectedRetainedScaledProfile_inputs
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)
    (η : EvenIdealRayCharacter K J) (hJ : J ≠ ⊥)
    (hT : 2 < T) (p : SourceKPPositiveSeedData K hζ S₀ hS hJ hT)
    (u : ExteriorUnitSixthClasses S) (v : InfinitePlace K) :
    sourceReflectionFiniteProfileInputs (sourceKPReflectedRetainedScaledProfile K hζ S₀ hS η hJ hT p u v) :=
  sourceKPRetainedThetaProfile_scaledOption_inputs K hζ S₀ hS η hJ (fun _ : I[p] => rep u)
    (fun i => pre[p] i p.a) v p.cutoff (fun l => sourceKPReflectedRetainedSeedScalar K hζ S₀ hS hJ hT p (l.1,l.2.1))

end
end ArtinMatthews
