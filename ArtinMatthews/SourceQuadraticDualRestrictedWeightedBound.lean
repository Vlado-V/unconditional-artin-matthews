module

public import ArtinMatthews.SourceQuadraticDualRestrictedContour
public import ArtinMatthews.SourceReflectionDyadicIndex
public import ArtinMatthews.SourceQuadraticDualRestrictedBound
public import ArtinMatthews.SourceQuadraticDualWeightedPhase
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain MeasureTheory Set QuadraticScale StandardAdelic
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "E" => SourcePrimeExponents F S₀
local notation "q" => sourcePrimeExponentNorm F S₀
local notation "A" => quadraticHeckeFieldScale F
local notation "r" => InfinitePlace.nrComplexPlaces F

theorem sourceQuadraticDualRestrictedContour_weighted_bound {α : ℝ} (hα : 1 ≤ α)
    (htrace : traceBadPlaces F ⊆ sourceHilbertSet F S₀)
    (hE : QuadraticHeckeSieveExponentBound (sourceQuadraticDyadicEnergy F S₀ hζ) α)
    (η : ℝ) (hη : 0 < η) {σ : ℝ} (hσ : 0 < σ) (hσ₁ : σ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ L K P X B : ℝ, 0 < L → 1 ≤ K → 1 ≤ P → 0 < X → 1 ≤ B →
      ∀ rows cols : Finset E,
      (∀ a ∈ rows, sourceReflectionIsSquarefree a ∧ L ≤ (q a : ℝ) ∧ (q a : ℝ) ≤ K) →
      (∀ b ∈ cols, sourceReflectionIsSquarefree b ∧ P ≤ (q b : ℝ) ∧ (q b : ℝ) ≤ 2*P) →
      (∀ b ∈ cols, ∀ c ∈ cols,
        sourceQuadraticLocalClass F S₀ hζ b = sourceQuadraticLocalClass F S₀ hζ c) →
      ∀ (u : E → ℂ) (g d : E),
      ‖sourceQuadraticDualRestrictedContour F S₀ hζ rows cols u g d X B σ‖ ≤
        C * X^(1-σ/2) * (P/(q g : ℝ))^(σ-1) *
          (2*K*P)^η * (2*P)^η * (sourceReflectionDyadLength K : ℝ) *
          (2*P*L^(-(σ/2))+(2:ℝ)^α*K^(α-σ/2)) * coeffMass cols u := by
  obtain ⟨Ca, hCa, ha⟩ := sourceQuadraticDualPairAmplitude_weighted_bound F S₀ hζ hα htrace hE η hη
  let H := quadraticDualContourKernel F A r sourceQuadraticBlockProfile σ
  let L₀ : ℝ := 1 + ∫ t : ℝ, ‖H t‖
  have hL₀ : 0 < L₀ := by
    have hn : 0 ≤ ∫ t : ℝ, ‖H t‖ := integral_nonneg (fun _ => norm_nonneg _)
    dsimp [L₀]
    linarith
  refine ⟨L₀*Ca, by positivity, ?_⟩
  intro L K P X B hL hK hP hX hB rows cols hrows hcols hclass u g d
  let D := Ca * X^(1-σ/2) * (P/(q g : ℝ))^(σ-1) *
    (2*K*P)^η * (2*P)^η * (sourceReflectionDyadLength K : ℝ) *
          (2*P*L^(-(σ/2))+(2:ℝ)^α*K^(α-σ/2)) * coeffMass cols u
  have hmass : 0 ≤ coeffMass cols u := coeffMass_nonneg _ _
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hamp (t : ℝ) : ‖sourceQuadraticDualPairAmplitude F S₀ hζ rows cols u g d X
      (quadraticPoissonLine σ t)‖ ≤ D := by
    simpa only [quadraticPoissonLine_re] using
      ha L K P X hL hK hP hX rows cols hrows hcols hclass u g d
        (quadraticPoissonLine σ t) (by rw [quadraticPoissonLine_re]; exact hσ.le)
        (by rw [quadraticPoissonLine_re]; exact hσ₁.le)
  calc
    _ ≤ (∫ t : ℝ, ‖H t‖) * D :=
      sourceQuadraticDualRestrictedContour_norm_le F S₀ hζ rows cols u g d hX hB hσ hσ₁ hamp
    _ ≤ L₀*D := mul_le_mul_of_nonneg_right (by dsimp [L₀]; linarith) hD
    _ = _ := by dsimp [D]; ring

end
end ArtinMatthews.SourceEulerAssembly
