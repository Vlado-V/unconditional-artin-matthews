module

public import ArtinMatthews.SourceKPResidualWirtingerTheta
public import ArtinMatthews.SourceKPPhysicalHorizontal
public import ArtinMatthews.SourceKPResidualSmoothRepresentative
public import ArtinMatthews.SourceKPAdelicCompactIntersection
public import ArtinMatthews.SourceKPResidualSmoothFourier
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

/-! The normalized physical derivative has its exact all-frequency
Bessel expansion for every S-local point and every finite translate. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain SourceReflection SourceHyperbolicGreen
open scoped NumberField Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
local notation "V" => InfinitePlace K
local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "L" => sourceKPAllInfinitePlaces K

theorem sourceKPSLocalHeight_frequency (S : Finset (HeightOneSpectrum (𝓞 K)))
    (m : Kˣ) (x : SWholeUnits K S) :
    sourceKPCuspRationalHeight K hζ m (sourceKPSLocalHeight K S x) =
      sourceKPSLocalHeight K S (sWholeDiagonal K S m * x) := by
  funext v
  let u : v.Completionˣ := Units.map (algebraMap K v.Completion).toMonoidHom m
  have h : (sourceKPCuspRationalComplexUnit K hζ m v : ℂ) =
      sourceKPArchComplexEquiv K hζ v (u : v.Completion) := rfl
  change ‖(sourceKPCuspRationalComplexUnit K hζ m v : ℂ)‖ * ‖(x.1 v : v.Completion)‖ =
    ‖((u * x.1 v : v.Completionˣ) : v.Completion)‖
  rw [h,sourceKPArchComplexEquiv_norm,Units.val_mul,norm_mul]

def sourceKPPhysicalResidualBesselTerm (S : Finset (HeightOneSpectrum (𝓞 K)))
    (ε : V → Bool) {T : ℝ} (hT : 1 ≤ T) (g : Gf) (m : Kˣ) (x : SWholeUnits K S) : ℂ :=
  sourceKPCuspResidualFourierValue K hζ 1 hT (sourceKPCuspResidualUnitTranslate K hζ m g) *
    sourceKPResidualArchAngular K ε m *
    ∏ v : V, sourceThetaBesselProfile (4*Real.pi) ((sourceKPSLocalHeight K S (sWholeDiagonal K S m*x) v)^2)

theorem sourceKPPhysicalResidualBesselTerm_hasSum (S : Finset (HeightOneSpectrum (𝓞 K)))
    (ε : V → Bool) {T : ℝ} (hT : 1 ≤ T) (g : Gf) (x : SWholeUnits K S) :
    HasSum (fun m : Kˣ => sourceKPPhysicalResidualBesselTerm K hζ S ε hT g m x)
      ((sourceKPResidualArchDerivativeConstant K)⁻¹ *
        sourceProductHorizontalList ε L
          (sourceKPCompactChartPullback K hζ (sourceKPResidualSmoothRepresentative K hζ hT)
            (QuotientGroup.mk g)) (sourceKPCuspHeightPoint K (sourceKPSLocalHeight K S x))) := by
  let _ : IsTotallyComplex K := source_isTotallyComplex K hζ
  let y := sourceKPSLocalHeight K S x
  let C := sourceKPResidualArchDerivativeConstant K
  have hy : ∀ v, 0 < y v := sourceKPSLocalHeight_pos K S x
  have h := sourceKPResidualSmooth_horizontal_hasSum K hζ g hT ε L
    (sourceKPAllInfinitePlaces_ne_nil K) y hy
  have H := h.mul_left C⁻¹
  apply H.congr_fun
  intro m
  rw [sourceKPResidualWirtingerTheta_term K hζ ε m g hT y hy]
  change _ = C⁻¹ * (C * _ * _ * _)
  rw [sourceKPSLocalHeight_frequency K hζ S m x]
  unfold sourceKPPhysicalResidualBesselTerm
  simp only [mul_assoc]
  rw [inv_mul_cancel_left₀ (show C ≠ 0 from sourceKPResidualArchDerivativeConstant_ne_zero K)]

def sourceKPPhysicalResidualValue (S : Finset (HeightOneSpectrum (𝓞 K)))
    (ε : V → Bool) {T : ℝ} (hT : 1 ≤ T) (qf : Gf) (x : SWholeUnits K S) : ℂ :=
  (sourceKPResidualArchDerivativeConstant K)⁻¹ *
    sourceKPPhysicalHorizontalValue K hζ S ε L (sourceKPResidualSmoothRepresentative K hζ hT) qf x

theorem sourceKPPhysicalResidualValue_hasSum (S : Finset (HeightOneSpectrum (𝓞 K)))
    (ε : V → Bool) {T : ℝ} (hT : 1 ≤ T) (qf : Gf) (x : SWholeUnits K S) :
    HasSum (fun m : Kˣ => sourceKPPhysicalResidualBesselTerm K hζ S ε hT
      ((sourceSLocalProjectiveDiagonalLift K S hζ x).2*qf) m x)
      (sourceKPPhysicalResidualValue K hζ S ε hT qf x) :=
  sourceKPPhysicalResidualBesselTerm_hasSum K hζ S ε hT _ x

theorem sourceKPPhysicalResidualValue_reflection (S : Finset (HeightOneSpectrum (𝓞 K)))
    (b : Kˣ) (ε : V → Bool) {T : ℝ} (hT : 1 ≤ T) (qf : Gf) (x : SWholeUnits K S) :
    let a := sourceKPSLocalReflectionArgument K S b
    let y := a*x⁻¹
    HasSum (fun m : Kˣ => sourceKPPhysicalResidualBesselTerm K hζ S (fun v => !(ε v)) hT
      (sourceKPReflectedHorizontalFiber K hζ S b qf y) m y)
      ((sourceKPReflectionProductPhase K hζ b ε L)⁻¹ *
        sourceKPPhysicalResidualValue K hζ S ε hT qf x) := by
  let _ : IsTotallyComplex K := source_isTotallyComplex K hζ
  let W := sourceKPResidualSmoothRepresentative K hζ hT
  let a := sourceKPSLocalReflectionArgument K S b
  let y := a*x⁻¹
  let g := sourceKPReflectedHorizontalFiber K hζ S b qf y
  let ω := sourceKPReflectionProductPhase K hζ b ε L
  have hω : ω ≠ 0 := by
    apply norm_ne_zero_iff.mp
    change ‖sourceKPReflectionProductPhase K hζ b ε L‖ ≠ 0
    rw [sourceKPReflectionProductPhase_norm K hζ b ε L]
    exact one_ne_zero
  have h := sourceKPPhysicalResidualBesselTerm_hasSum K hζ S (fun v => !(ε v)) hT g y
  have hr := sourceKPPhysicalHorizontalValue_reflection K hζ S b ε L
    (sourceKPAllInfinitePlaces_nodup K) W (sourceKPResidualSmoothRepresentative_chart K hζ hT) qf x
  change HasSum _ (ω⁻¹ * sourceKPPhysicalResidualValue K hζ S ε hT qf x)
  rw [sourceKPPhysicalResidualValue,hr]
  change HasSum _ (ω⁻¹ * ((sourceKPResidualArchDerivativeConstant K)⁻¹ *
    (ω * sourceKPReflectedHorizontalValue K hζ S b ε L W qf y)))
  rw [show ω⁻¹ * ((sourceKPResidualArchDerivativeConstant K)⁻¹ *
      (ω * sourceKPReflectedHorizontalValue K hζ S b ε L W qf y)) =
      (sourceKPResidualArchDerivativeConstant K)⁻¹ *
        sourceKPReflectedHorizontalValue K hζ S b ε L W qf y by
      rw [mul_left_comm,inv_mul_cancel_left₀ hω]]
  exact h

end
end ArtinMatthews
