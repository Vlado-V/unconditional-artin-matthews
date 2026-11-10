module

public import ArtinMatthews.SourceKPReflectedPhysicalBranch
public import ArtinMatthews.SourceKPPhysicalNegativePhase
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

/-! Isolate the finite coefficient in each actual reflected term before
changing its S-local frequency variable. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain QuadraticWeil VaryingKummerAnalytic
open SourcePhysical SourceReflection SourceEulerAssembly
open scoped NumberField Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] {ζ : K}
    (hζ : IsPrimitiveRoot ζ 12) (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
local notation "S" => sourceHilbertSet K S₀
local notation "Whole" => SWholeUnits K S
local notation "E" => SourcePrimeExponents K S₀
local notation "PE" => SourceExteriorPrime K S₀
local notation "D" => sWholeDiagonal K S
local notation "angle" => sourceKPOrientedHorizontal K hζ
local notation "rep" => sourceExteriorUnitSixthRepresentative S
local notation "Weight" => sourceKPPhysicalRowWeight K hζ S₀
local notation "Mask" => sourceKPPositivePhysicalActiveMask K S₀
local notation "arg" => sourceKPSLocalReflectionArgument K S
local notation "ω" => fun b => sourceKPReflectionProductPhase K hζ b angle (sourceKPAllInfinitePlaces K)
def sourceKPReflectedArchBesselFactor (z : Whole) : ℂ :=
  ∏ v : InfinitePlace K, sourceThetaArchFactor K v (4*Real.pi) (z.1 v)

local notation "Arch" => sourceKPReflectedArchBesselFactor K S₀

attribute [local instance] positiveTwistLabelFintype
variable {J : Ideal (𝓞 K)}

def sourceKPReflectedPhysicalFiniteCoefficient
    (hS : standardWeilBadPlaces K ⊆ S) (hJ : J ≠ ⊥)
    {T : ℝ} (hT : 2 < T) (p : SourceKPPositiveSeedData K hζ S₀ hS hJ hT)
    (e : E) (active : Finset PE) (b m : Kˣ) (x : Whole) : ℂ :=
  let q₀ := sourceKPPositiveSeedData_q₀ K hζ S₀ p
  let t := one_le_two.trans hT.le
  ∑ i : SourceReflectionPositiveTwistLabels K S₀ e × SourceKPRetainedSeedIndex K S p.R p.M,
    sourceKPPositivePhysicalTranslateWeight K hζ S₀ e p.R p.M (Mask e active) i *
      sourceKPCuspResidualFourierValue K hζ 1 t
        (sourceKPCuspResidualUnitTranslate K hζ m
          (sourceKPReflectedHorizontalFiber K hζ S b
            (sourceKPPositivePhysicalTranslate K hζ S₀ e p.R p.M q₀ i) x))

def sourceKPReflectedPhysicalBranchTerm
    (hS : standardWeilBadPlaces K ⊆ S) (η : EvenIdealRayCharacter K J) (hJ : J ≠ ⊥)
    {T : ℝ} (hT : 2 < T) (p : SourceKPPositiveSeedData K hζ S₀ hS hJ hT)
    (e : E) (u : ExteriorUnitSixthClasses S) (active : Finset PE) (b m : Kˣ) (x : Whole) : ℂ :=
  let q₀ := sourceKPPositiveSeedData_q₀ K hζ S₀ p
  let t := one_le_two.trans hT.le
  Weight hS η hJ (rep u) (arg b*x⁻¹) * (sourceKPCuspResidualFourierValue K hζ 1 t q₀)⁻¹ *
    sourceKPReflectedPhysicalFiniteCoefficient K hζ S₀ hS hJ hT p e active b m x *
    sourceKPResidualArchAngular K (fun v => !(angle v)) m * Arch (D m*x)

theorem sourceKPReflectedPhysicalBranchTerm_hasSum
    (hS : standardWeilBadPlaces K ⊆ S) (η : EvenIdealRayCharacter K J) (hJ : J ≠ ⊥)
    {T : ℝ} (hT : 2 < T) (p : SourceKPPositiveSeedData K hζ S₀ hS hJ hT)
    (e : E) (u : ExteriorUnitSixthClasses S) (active : Finset PE) (b : Kˣ) (x : Whole) :
    HasSum (fun m => sourceKPReflectedPhysicalBranchTerm K hζ S₀ hS η hJ hT p e u active b m x)
      (sourceKPReflectedPhysicalBranchValue K hζ S₀ hS η hJ hT p e u active b x) := by
  have h := sourceKPReflectedPhysicalBranchValue_hasSum K hζ S₀ hS η hJ hT p e u active b x
  dsimp only at h
  apply h.congr_fun
  intro m
  dsimp only [sourceKPReflectedPhysicalBranchTerm,sourceKPReflectedPhysicalFiniteCoefficient,
    sourceKPPhysicalResidualBesselTerm]
  simp_rw [← mul_assoc, ← Finset.sum_mul]
  simp only [sourceKPReflectedArchBesselFactor,sourceThetaArchFactor,sourceSheetArchNorm,sourceKPSLocalHeight,mul_assoc]

theorem sourceKPReflectedPhysicalBranchTerm_weight
    (hS : standardWeilBadPlaces K ⊆ S) (η : EvenIdealRayCharacter K J) (hJ : J ≠ ⊥)
    {T : ℝ} (hT : 2 < T) (p : SourceKPPositiveSeedData K hζ S₀ hS hJ hT)
    (e : E) (u : ExteriorUnitSixthClasses S) (active : Finset PE) (b m : Kˣ) (x : Whole) :
    let q₀ := sourceKPPositiveSeedData_q₀ K hζ S₀ p
    let t := one_le_two.trans hT.le
    let z := D m*x
    ω b * sourceKPReflectedPhysicalBranchTerm K hζ S₀ hS η hJ hT p e u active b m x =
      sourceKPPhysicalNegativePhase K hζ S₀ hS η hJ (rep u) b (D m) *
      (sourceKPCuspResidualFourierValue K hζ 1 t q₀)⁻¹ *
      sourceKPAllowedClassGate K hζ S₀ (arg b*x⁻¹) *
      (sourceKPPhysicalRowFiniteCharacter K hζ S₀ hS η hJ (rep u) z : ℂ) *
      sourceKPReflectedPhysicalFiniteCoefficient K hζ S₀ hS hJ hT p e active b m x * Arch z := by
  let q₀ := sourceKPPositiveSeedData_q₀ K hζ S₀ p
  let t := one_le_two.trans hT.le
  let C₀ := sourceKPCuspResidualFourierValue K hζ 1 t q₀
  let w := Weight hS η hJ (rep u) (arg b*x⁻¹)
  let A := sourceKPResidualArchAngular K (fun v => !(angle v)) m
  let F := sourceKPReflectedPhysicalFiniteCoefficient K hζ S₀ hS hJ hT p e active b m x
  let B := Arch (D m*x)
  have hw := sourceKPPhysicalRowWeight_reflected_frequency K hζ S₀ hS η hJ (rep u) (arg b) x m
  change w*A = _ at hw
  calc
    _ = ω b * (w*A) * C₀⁻¹ * F * B := by
      change ω b * (w * C₀⁻¹ * F * A * B) = _
      ring
    _ = _ := by
      rw [hw]
      dsimp only [sourceKPPhysicalNegativePhase,C₀,F,B,q₀,t]
      ring

end
end ArtinMatthews
