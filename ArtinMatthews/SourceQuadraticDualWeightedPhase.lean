module

public import ArtinMatthews.SourceQuadraticDualPairAmplitude
public import ArtinMatthews.SourceReflectionDyadicIndex
public import ArtinMatthews.SourcePrimeNormSummability
public import ArtinMatthews.SourceQuadraticDualPhaseBound
public import ArtinMatthews.SourceQuadraticDualWeightedRows
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
open NumberField IsDedekindDomain QuadraticScale StandardAdelic
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "E" => SourcePrimeExponents F S₀
local notation "q" => sourcePrimeExponentNorm F S₀

theorem sourceQuadraticDualPairAmplitude_weighted_bound {α : ℝ} (hα : 1 ≤ α)
    (htrace : traceBadPlaces F ⊆ sourceHilbertSet F S₀)
    (hE : QuadraticHeckeSieveExponentBound (sourceQuadraticDyadicEnergy F S₀ hζ) α)
    (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ L K P X : ℝ, 0 < L → 1 ≤ K → 1 ≤ P → 0 < X →
      ∀ rows cols : Finset E,
      (∀ a ∈ rows, sourceReflectionIsSquarefree a ∧ L ≤ (q a : ℝ) ∧ (q a : ℝ) ≤ K) →
      (∀ b ∈ cols, sourceReflectionIsSquarefree b ∧ P ≤ (q b : ℝ) ∧ (q b : ℝ) ≤ 2*P) →
      (∀ b ∈ cols, ∀ c ∈ cols,
        sourceQuadraticLocalClass F S₀ hζ b = sourceQuadraticLocalClass F S₀ hζ c) →
      ∀ (u : E → ℂ) (g d : E) (s : ℂ), 0 ≤ s.re → s.re ≤ 1 →
      ‖sourceQuadraticDualPairAmplitude F S₀ hζ rows cols u g d X s‖ ≤
        C * X ^ (1-s.re/2) * (P/(q g : ℝ)) ^ (s.re-1) *
          (2*K*P)^η * (2*P)^η * (sourceReflectionDyadLength K : ℝ) *
          (2*P*L^(-(s.re/2))+(2:ℝ)^α*K^(α-s.re/2)) * coeffMass cols u := by
  obtain ⟨C, hC, hbound⟩ := sourceQuadraticDualEulerRowSum_weighted_bound F S₀ hζ hα htrace hE η hη
  refine ⟨C, hC, ?_⟩
  intro L K P X hL hK hP hX rows cols hrows hcols hclass u g d s hs hs₁
  let R := P / (q g : ℝ)
  have hR : 0 < R := div_pos (zero_lt_one.trans_le hP)
    (Nat.cast_pos.mpr (sourcePrimeExponentNorm_pos F S₀ g))
  let res := sourceQuadraticSmallResidualColumns F S₀ cols g
  let v := sourceQuadraticSmallResidualCoeff F S₀ g u
  have hres (b : E) (hb : b ∈ res) :
      sourceReflectionIsSquarefree b ∧ (q b : ℝ) ≤ 2*P :=
    ⟨sourceQuadraticSmallResidualColumns_squarefree F S₀ cols g (fun c hc => (hcols c hc).1) b hb,
      sourceQuadraticSmallResidualColumns_norm F S₀ cols g (2*P)
        (fun c hc => (hcols c hc).2.2) b hb⟩
  have hnorm (z : ℂ) (hz : z.re ≤ 1) (b : E) (hb : b ∈ res) :
      ‖sourceQuadraticDualColumnPhase F S₀ hζ u g d R z b‖ ≤ ‖v b‖ :=
    sourceQuadraticDualColumnPhase_norm_le F S₀ hζ u g d b hR
      (sourceQuadraticDualResidualColumns_lower F S₀ cols g (fun c hc => (hcols c hc).2.1) b hb) hz
  have hsum := hbound L K P hL hK hP rows res hrows hres v
    (sourceQuadraticDualColumnPhase F S₀ hζ u g d R (star s))
    (sourceQuadraticDualColumnPhase F S₀ hζ u g d R s)
    (hnorm (star s) (by simpa using hs₁)) (hnorm s hs₁) s hs hs₁
  have hmass := sourceQuadraticSmallResidualCoeff_mass F S₀ cols g u
  rw [sourceQuadraticDualPairAmplitude_separate F S₀ hζ rows cols
    (fun b hb => (hcols b hb).1) hclass u g d hX hR s, norm_mul, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hX, Complex.norm_cpow_eq_rpow_re_of_pos hR]
  have hr1 : (1-s/2).re = 1-s.re/2 := by simp
  have hr2 : (s-1).re = s.re-1 := by simp
  rw [hr1, hr2]
  calc
    _ ≤ X ^ (1-s.re/2) * R ^ (s.re-1) *
        (C * (2*K*P)^η * (2*P)^η * (sourceReflectionDyadLength K : ℝ) *
          (2*P*L^(-(s.re/2))+(2:ℝ)^α*K^(α-s.re/2)) * coeffMass res v) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ X ^ (1-s.re/2) * R ^ (s.re-1) *
        (C * (2*K*P)^η * (2*P)^η * (sourceReflectionDyadLength K : ℝ) *
          (2*P*L^(-(s.re/2))+(2:ℝ)^α*K^(α-s.re/2)) * coeffMass cols u) := by
      gcongr
    _ = _ := by dsimp [R]; ring

end
end ArtinMatthews.SourceEulerAssembly
