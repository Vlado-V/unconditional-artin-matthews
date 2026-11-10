module

public import ArtinMatthews.SourceQuadraticCutoffMainBound
public import ArtinMatthews.QuadraticHeckeCutoffWeightBounds
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
open NumberField IsDedekindDomain StandardAdelic VaryingKummerAnalytic
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "E" => SourcePrimeExponents F S₀
local notation "q" => sourcePrimeExponentNorm F S₀
local notation "I" => sourcePrimeExponentIdeal F S₀
local notation "χ" => sourceReflectionQuadraticSymbol F S₀ hζ

/-- The omitted ideal weight paired with genuine source quadratic column twists. -/
def sourceQuadraticActualCutoffMainSum (g : Ideal (𝓞 F)) (H : ℝ) (rows cols : Finset E)
    (twistIndex : Ideal (𝓞 F) → Ideal (𝓞 F) → E) (coeff : E → ℂ) : ℂ :=
  sourceQuadraticCutoffMainSum F S₀ hζ g rows cols
    (fun d e h => quadraticHeckeCutoffWeight F H (I h) d e)
    (fun d e b => χ (twistIndex d e) b) coeff

variable [IsTotallyComplex F]

/-- GL7.3 for the actual cutoff weight and source quadratic characters. -/
theorem sourceQuadraticActualCutoffMainSum_bound {α : ℝ}
    (htrace : traceBadPlaces F ⊆ sourceHilbertSet F S₀)
    (hE : QuadraticHeckeSieveExponentBound (sourceQuadraticDyadicEnergy F S₀ hζ) α)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M P H : ℝ), 1 ≤ M → 1 ≤ P → 1 ≤ H → H ≤ M →
      ∀ (g : Ideal (𝓞 F)), Squarefree g → ∀ (rows cols : Finset E),
      (∀ h ∈ rows, sourceReflectionIsSquarefree h ∧ (q h : ℝ) ≤ H) →
      (∀ b ∈ cols, sourceReflectionIsSquarefree b ∧ (q b : ℝ) ≤ P) →
      ∀ (twistIndex : Ideal (𝓞 F) → Ideal (𝓞 F) → E) (coeff : E → ℂ),
      ‖(Real.sqrt M : ℂ) * sourceQuadraticActualCutoffMainSum F S₀ hζ g H rows cols twistIndex coeff‖ ≤
        C * (Ideal.absNorm g : ℝ) ^ 4 * (M * P) ^ ε *
          (Real.sqrt M * H ^ (α - 1 / 2) + Real.sqrt (M / H) * P) *
            ∑ b ∈ cols, ‖coeff b‖ ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := sourceQuadraticCutoffMainSum_bound F S₀ hζ htrace hE ε hε
  refine ⟨C, hC, ?_⟩
  intro M P H hM hP hH hHM g hg rows cols hrows hcols twistIndex coeff
  apply hbound M P H hM hP hH hHM g hg rows cols hrows hcols
  · intro d _ e he h _
    exact quadraticHeckeCutoffWeight_norm_le F (zero_lt_one.trans_le hH) (I h) d e
      (ne_zero_of_dvd_ne_zero hg.ne_zero ((HeckeIdealMobius.mem_divisors F hg.ne_zero).1 he))
  · intro d _ e _ b _
    exact sourceReflectionQuadraticSymbol_norm_le_one F S₀ hζ (twistIndex d e) b

end
end ArtinMatthews.SourceEulerAssembly
