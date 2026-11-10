module

public import ArtinMatthews.SourceQuadraticClassFactorization
public import ArtinMatthews.SourceQuadraticCommonGram
public import ArtinMatthews.QuadraticB3PairMass
public import ArtinMatthews.SourceReflectionExteriorRows
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
open NumberField IsDedekindDomain QuadraticScale
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
local notation "E" => SourcePrimeExponents F S₀
local notation "q" => sourcePrimeExponentNorm F S₀

/-- The actual ideal count controls every subset of pairs in a column norm ball. -/
theorem sourceQuadraticPairMass_bound :
    ∃ A : ℝ, 0 < A ∧ ∀ (P : ℝ), 1 ≤ P → ∀ D : Finset E,
      (∀ b ∈ D, (q b : ℝ) ≤ 2 * P) → ∀ pairs : Finset (E × E),
      pairs ⊆ D ×ˢ D → ∀ a : E → ℂ,
      (∑ p ∈ pairs, ‖star (a p.1) * a p.2‖) ≤ A * P * coeffMass D a := by
  obtain ⟨C, hC, hcount⟩ := exists_sourceReflectionExteriorCard_le F S₀
  refine ⟨2 * C, by positivity, ?_⟩
  intro P hP D hD pairs hpairs a
  have hcard : (D.card : ℝ) ≤ C * (2 * P) :=
    hcount (2 * P) (by linarith) D hD
  calc
    _ ≤ (D.card : ℝ) * coeffMass D a := pairCoefficientMass_le D pairs hpairs a
    _ ≤ (C * (2 * P)) * coeffMass D a :=
      mul_le_mul_of_nonneg_right hcard (coeffMass_nonneg D a)
    _ = _ := by ring

/-- The same bound applies to the literal ray-class, common-ideal, off-diagonal pairs. -/
theorem sourceQuadraticRayOffDiagonalPairMass_bound :
    ∃ A : ℝ, 0 < A ∧ ∀ (P : ℝ), 1 ≤ P → ∀ cols : Finset E,
      (∀ b ∈ cols, (q b : ℝ) ≤ 2 * P) →
      ∀ (κ : SourceQuadraticRayClass F S₀) (g : E) (a : E → ℂ),
      let D := sourceQuadraticClassColumns F S₀ cols (sourcePrimeExponentRayClass F S₀) κ
      (∑ p ∈ (D ×ˢ D).filter (fun p : E × E => p.1 ⊓ p.2 = g ∧ p.1 ≠ p.2),
        ‖star (a p.1) * a p.2‖) ≤ A * P * coeffMass D a := by
  obtain ⟨A, hA, hbound⟩ := sourceQuadraticPairMass_bound F S₀
  refine ⟨A, hA, ?_⟩
  intro P hP cols hcols κ g a
  dsimp only
  apply hbound P hP _ _ _ (Finset.filter_subset _ _) a
  intro b hb
  exact hcols b (Finset.mem_filter.mp hb).1

end
end ArtinMatthews.SourceEulerAssembly
