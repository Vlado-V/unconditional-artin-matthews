module

public import ArtinMatthews.SourceThetaPositiveSheet
public import ArtinMatthews.SourceKPPositiveSeedPhysicalCoefficient
public import ArtinMatthews.SourceKPPhysicalRowWeight
public import ArtinMatthews.SourceKPAllowedSquarefreeCube
public import ArtinMatthews.SourceKPAllowedForwardOrbit
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

/-! The actual forward physical Fourier series becomes a periodized
positive tensor with literal squarefree and cube exterior coordinates. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain QuadraticWeil AllowedGenerators
open VaryingKummerAnalytic SourcePhysical SourceReflection
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
local notation "freq" => sourceKPAllowedSquarefreeCubeFieldEquiv K hζ S₀
local notation "ε" => sourceKPOrientedHorizontal K hζ
local notation "Wext" => sourceKPRetainedExteriorWhittaker K hζ S₀

variable {J : Ideal (𝓞 K)}

theorem sourceKPPositivePhysicalFiniteTerm_weighted
    (hS : standardWeilBadPlaces K ⊆ S) (η : EvenIdealRayCharacter K J) (hJ : J ≠ ⊥)
    (u : ↥(exteriorUnitSubgroup (sourceHilbertSet K S₀))) {T : ℝ} (hT : 2 < T)
    (p : SourceKPPositiveSeedData K hζ S₀ hS hJ hT) (e : E)
    (mask : SourceReflectionPositiveTwistLabels K S₀ e → ℂ) (m : Kˣ) (x : Whole) :
    let q₀ := sourceKPPositiveSeedData_q₀ K hζ S₀ p
    let weight := sourceKPPhysicalRowWeight K hζ S₀ hS η hJ u
    let Χ := sourceKPPhysicalRowWholeCharacter K hζ S₀ hS η hJ u
    let τ := sourceKPPositivePhysicalTwistScalar K hζ S₀ e mask
    sourceKPPositivePhysicalFiniteTerm K hζ S₀ e p.R p.M ε (one_le_two.trans hT.le) q₀ mask weight m x =
      if m ∈ allowedSubgroup K hζ S₀ then
        (Χ (D m) : ℂ) * τ m * Wext hS m *
          sourceThetaPositiveTensor K S (fun _ => 4*Real.pi) p.cutoff (D m*x)
      else 0 := by
  let q₀ := sourceKPPositiveSeedData_q₀ K hζ S₀ p
  let t := one_le_two.trans hT.le
  let C₀ := sourceKPCuspResidualFourierValue K hζ 1 t q₀
  let A := sourceKPResidualArchAngular K ε m
  let F := ∏ P : S, (p.cutoff P).factor ((D m*x).2 P)
  let B := ∏ v : InfinitePlace K, sourceThetaArchFactor K v (4*Real.pi) ((D m*x).1 v)
  let weight := sourceKPPhysicalRowWeight K hζ S₀ hS η hJ u x
  let χ := sourceKPPhysicalRowWholeCharacter K hζ S₀ hS η hJ u
  let τ := sourceKPPositivePhysicalTwistScalar K hζ S₀ e mask m
  let W := Wext hS m
  have hC : C₀ ≠ 0 := p.coefficient_ne_zero
  have hc : sourceKPPositivePhysicalFiniteCoefficient K hζ S₀ e p.R p.M t q₀ mask m x =
      τ*(C₀*F*W) := sourceKPPositivePhysicalSeedCoefficient K hζ S₀ hS hJ hT p e mask m x
  have hweight : weight * A * F = if m ∈ allowedSubgroup K hζ S₀ then (χ (D m) : ℂ)*F else 0 :=
    sourceKPPhysicalRowWeight_positive_frequency K hζ S₀ hS η hJ u p.cutoff p.depth m x
  change weight * C₀⁻¹ * sourceKPPositivePhysicalFiniteCoefficient K hζ S₀ e p.R p.M t q₀ mask m x * A * B =
    if m ∈ allowedSubgroup K hζ S₀ then (χ (D m) : ℂ)*τ*W*(B*F) else 0
  rw [hc]
  calc
    _ = (weight*A*F)*(τ*W*B) := by field_simp [hC]
    _ = _ := by
      rw [hweight]
      split
      · ring
      · rw [zero_mul]

theorem sourceKPPositivePhysicalFiniteValue_orbit
    (hS : standardWeilBadPlaces K ⊆ S) (η : EvenIdealRayCharacter K J) (hJ : J ≠ ⊥)
    (u : ↥(exteriorUnitSubgroup (sourceHilbertSet K S₀))) {T : ℝ} (hT : 2 < T)
    (p : SourceKPPositiveSeedData K hζ S₀ hS hJ hT) (e : E)
    (mask : SourceReflectionPositiveTwistLabels K S₀ e → ℂ) (a : C × E → ℂ)
    (ha : ∀ (c : C) (n : E) (γ : Γ),
      let m := (freq ((c,n),γ)).val
      (sourceKPPhysicalRowWholeCharacter K hζ S₀ hS η hJ u (D m) : ℂ) *
        sourceKPPositivePhysicalTwistScalar K hζ S₀ e mask m * Wext hS m = a (c,n))
    (x : Whole) :
    let q₀ := sourceKPPositiveSeedData_q₀ K hζ S₀ p
    let weight := sourceKPPhysicalRowWeight K hζ S₀ hS η hJ u
    HasSum (fun z : (C × E) × Γ => a z.1 *
      sourceThetaPositiveTensor K S (fun _ => 4*Real.pi) p.cutoff
        ((x*(z.2.val : Whole))*D (gen (z.1.1.val + 3 • z.1.2))))
      (sourceKPPositivePhysicalFiniteValue K hζ S₀ e p.R p.M ε (one_le_two.trans hT.le) q₀ mask weight x) := by
  let q₀ := sourceKPPositiveSeedData_q₀ K hζ S₀ p
  let t := one_le_two.trans hT.le
  let weight := sourceKPPhysicalRowWeight K hζ S₀ hS η hJ u
  let F (m : Kˣ) := sourceKPPositivePhysicalFiniteTerm K hζ S₀ e p.R p.M ε t q₀ mask weight m x
  have hf := sourceKPPositivePhysicalFiniteValue_hasSum K hζ S₀ e p.R p.M ε t q₀ mask weight x
  have hzero (m : Kˣ) (hm : m ∉ sourceKPAllowedFieldSupport K hζ S₀ (sourceKPPositiveCubeSupport K S₀)) :
      F m = 0 := by
    unfold F
    rw [sourceKPPositivePhysicalFiniteTerm_weighted K hζ S₀ hS η hJ u hT p e mask m x]
    by_cases hma : m ∈ allowedSubgroup K hζ S₀
    · rw [if_pos hma,sourceKPRetainedExteriorWhittaker_zero_off_allowed_support K hζ S₀ hS m hma hm,
        mul_zero,zero_mul]
    · rw [if_neg hma]
  have h := sourceKPAllowedSquarefreeCube_hasSum K hζ S₀ hf hzero
  apply h.congr_fun
  rintro ⟨⟨c,n⟩,γ⟩
  let m := freq ((c,n),γ)
  change _ = F m.val
  unfold F
  rw [sourceKPPositivePhysicalFiniteTerm_weighted K hζ S₀ hS η hJ u hT p e mask m.val x,
    if_pos m.property.1,ha c n γ,sourceKPAllowedSquarefreeCubeFieldEquiv_diagonal K hζ S₀ c n γ]
  congr 2
  ac_rfl

end
end ArtinMatthews
