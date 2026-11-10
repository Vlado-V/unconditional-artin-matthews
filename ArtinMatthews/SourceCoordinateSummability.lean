module

public import ArtinMatthews.FiniteSupportSourceCoordinates
public import ArtinMatthews.SourcePrimeExponents
public import ArtinMatthews.AbsoluteFourProduct
public import ArtinMatthews.SourcePrimeNormSummability
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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

/-! The genuine product of four Dedekind norm majorants on the source
index, with the squarefree coordinate and all shared prime factors retained. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain AllowedGenerators
open scoped NumberField Classical
noncomputable section
variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))

abbrev SourceExponentCoordinates := SourceEuler.SourceCoordinates (SourceExteriorPrime F S₀)

def sourceCoordinateMajorant (α β γ δ : ℝ) (a : SourceExponentCoordinates F S₀) : ℝ :=
  (sourcePrimeExponentNorm F S₀ a.1.val : ℝ) ^ (-α) *
    ((sourcePrimeExponentNorm F S₀ a.2.1 : ℝ) ^ (-β) *
      ((sourcePrimeExponentNorm F S₀ a.2.2.1 : ℝ) ^ (-γ) *
        (sourcePrimeExponentNorm F S₀ a.2.2.2 : ℝ) ^ (-δ)))

theorem sourceCoordinateMajorant_summable {α β γ δ : ℝ}
    (hα : 1 < α) (hβ : 1 < β) (hγ : 1 < γ) (hδ : 1 < δ) :
    Summable (sourceCoordinateMajorant F S₀ α β γ δ) := by
  exact SourceEuler.fourProduct_summable
    (fun c : {c : SourcePrimeExponents F S₀ // ∀ P, c P ≤ 1} =>
      (sourcePrimeExponentNorm F S₀ c.val : ℝ) ^ (-α))
    (fun n : SourcePrimeExponents F S₀ => (sourcePrimeExponentNorm F S₀ n : ℝ) ^ (-β))
    (fun s : SourcePrimeExponents F S₀ => (sourcePrimeExponentNorm F S₀ s : ℝ) ^ (-γ))
    (fun r : SourcePrimeExponents F S₀ => (sourcePrimeExponentNorm F S₀ r : ℝ) ^ (-δ))
    ((sourcePrimeExponentNorm_summable F S₀ hα).subtype (fun c => ∀ P, c P ≤ 1))
    (sourcePrimeExponentNorm_summable F S₀ hβ)
    (sourcePrimeExponentNorm_summable F S₀ hγ)
    (sourcePrimeExponentNorm_summable F S₀ hδ)

theorem sourceCoordinate_summable_of_bound (f : SourceExponentCoordinates F S₀ → ℂ)
    {α β γ δ : ℝ} (hα : 1 < α) (hβ : 1 < β) (hγ : 1 < γ) (hδ : 1 < δ)
    (hf : ∀ a, ‖f a‖ ≤ sourceCoordinateMajorant F S₀ α β γ δ a) : Summable f :=
  Summable.of_norm_bounded (sourceCoordinateMajorant_summable F S₀ hα hβ hγ hδ) hf

theorem sourceInitialCoordinateMajorant_summable :
    Summable (sourceCoordinateMajorant F S₀ (7 / 2) 10 3 12) :=
  sourceCoordinateMajorant_summable F S₀ (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end
end ArtinMatthews
