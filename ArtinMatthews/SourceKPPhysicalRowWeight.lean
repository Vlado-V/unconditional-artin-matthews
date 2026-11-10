module

public import ArtinMatthews.SourceKPPhysicalRowCharacter
public import ArtinMatthews.SourceKPAllowedClassGate
public import ArtinMatthews.SourceKPRetainedThetaDepth
public import ArtinMatthews.SourceKPRetainedThetaRowMultiplier
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
public import Std.Tactic.BVDecide.Normalize.Bool


set_option backward.privateInPublic true
@[expose] public section

/-! The positive physical weight is the literal allowed-class indicator
times the inverse retained theta and row characters. Its forward and
reflected frequency identities retain the same phases. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory AllowedGenerators QuadraticWeil
open VaryingKummerAnalytic SourceEulerAssembly SourceReflection AngularLambda SourcePhysical
open scoped NumberField Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] {ζ : K}
    (hζ : IsPrimitiveRoot ζ 12) (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
local notation "S" => sourceHilbertSet K S₀
local notation "U" => SWholeUnits K S
local notation "V" => InfinitePlace K
local notation "D" => sWholeDiagonal K S
local notation "gate" => sourceKPAllowedClassGate K hζ S₀
local notation "ε" => sourceKPOrientedHorizontal K hζ

variable (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)
variable {J : Ideal (𝓞 K)} (η : EvenIdealRayCharacter K J) (hJ : J ≠ ⊥)
variable (u : ↥(exteriorUnitSubgroup (sourceHilbertSet K S₀)))

include hζ hS η hJ u

local notation "χ" => sourceKPPhysicalRowFiniteCharacter K hζ S₀ hS η hJ u
local notation "Χ" => sourceKPPhysicalRowWholeCharacter K hζ S₀ hS η hJ u

def sourceKPPhysicalRowWeight (x : U) : ℂ :=
  gate x * ((χ x)⁻¹ : ℂˣ).val

theorem sourceKPPhysicalRowWeight_measurable [MeasurableSpace U] [BorelSpace U] :
    Measurable (sourceKPPhysicalRowWeight K hζ S₀ hS η hJ u) := by
  change Measurable (fun x : U => gate x * ((χ x)⁻¹ : ℂˣ).val)
  apply (sourceKPAllowedClassGate_measurable K hζ S₀).mul
  exact (Units.continuous_val.comp
    (sourceKPPhysicalRowFiniteCharacter_continuous K hζ S₀ hS η hJ u).inv).measurable

omit hζ hS η hJ u in
theorem sourceKPResidualArchAngular_flip (α : V → Bool) (m : Kˣ) :
    sourceKPResidualArchAngular K (fun v => !(α v)) m =
      (sourceKPResidualArchAngular K α m)⁻¹ := by
  unfold sourceKPResidualArchAngular
  rw [← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro v _
  cases h : α v <;> simp [h]

theorem sourceKPPhysicalRowWeight_reflected_frequency (a x : U) (m : Kˣ) :
    sourceKPPhysicalRowWeight K hζ S₀ hS η hJ u (a*x⁻¹) *
        sourceKPResidualArchAngular K (fun v => !(ε v)) m =
      gate (a*x⁻¹) * ((χ a)⁻¹ : ℂˣ).val * ((Χ (D m))⁻¹ : ℂˣ).val *
        (χ (D m*x) : ℂ) := by
  let A := sourceKPResidualArchAngular K ε m
  have hA : A ≠ 0 := by
    dsimp only [A]
    rw [sourceKPResidualArchAngular_oriented K hζ m]
    exact ((sourceReflectionAngularField K hζ m)⁻¹ : ℂˣ).ne_zero
  unfold sourceKPPhysicalRowWeight
  rw [sourceKPResidualArchAngular_flip K ε m]
  simp only [map_mul χ,map_inv χ,Units.val_inv_eq_inv_val,Units.val_mul]
  rw [sourceKPPhysicalRowWholeCharacter_diagonal K hζ S₀ hS η hJ u m]
  change gate (a*x⁻¹) * ((χ a : ℂ)*(χ x : ℂ)⁻¹)⁻¹ * A⁻¹ =
    gate (a*x⁻¹) * (χ a : ℂ)⁻¹ * ((χ (D m) : ℂ) * A)⁻¹ * ((χ (D m) : ℂ)*(χ x : ℂ))
  field_simp [hA,(χ a).ne_zero,(χ x).ne_zero,(χ (D m)).ne_zero]

theorem sourceKPPhysicalRowWeight_positive_frequency
    (W : ∀ P : S, SourceThetaFiniteCutoff K P.val)
    (hW : ∀ (P : S) (t : (P.val.adicCompletion K)ˣ), t ∈ (W P).region →
      ((t : P.val.adicCompletion K)-1) ∈ sourceLocalBall K P.val
        (-(sourceKPRetainedModulusDepth K S (sourceReflectionThetaModulus K S₀ hJ) P : ℤ)) ∧
        ∃ w, w^6 = t)
    (m : Kˣ) (x : U) :
    let F := ∏ P : S, (W P).factor ((D m*x).2 P)
    sourceKPPhysicalRowWeight K hζ S₀ hS η hJ u x *
        sourceKPResidualArchAngular K ε m * F =
      if m ∈ allowedSubgroup K hζ S₀ then (Χ (D m) : ℂ) * F else 0 := by
  let F := ∏ P : S, (W P).factor ((D m*x).2 P)
  let A := sourceKPResidualArchAngular K ε m
  have hg : gate x * F = if m ∈ allowedSubgroup K hζ S₀ then F else 0 :=
    sourceKPAllowedClassGate_mul_retainedProduct K hζ S₀ W (fun P t ht => (hW P t ht).2) m x
  have hc : ((χ x)⁻¹ : ℂˣ).val * F = (χ (D m) : ℂ) * F :=
    sourceKPRetainedThetaRowMultiplier_factor_product K hζ S₀ hS hJ η u W hW m x
  change (gate x * ((χ x)⁻¹ : ℂˣ).val) * A * F = _
  calc
    _ = gate x * (((χ x)⁻¹ : ℂˣ).val * F) * A := by ac_rfl
    _ = (χ (D m) : ℂ) * A * (gate x * F) := by rw [hc]; ac_rfl
    _ = _ := by
      rw [← sourceKPPhysicalRowWholeCharacter_diagonal K hζ S₀ hS η hJ u m,hg]
      split <;> first | rfl | simp only [mul_zero]

end
end ArtinMatthews
