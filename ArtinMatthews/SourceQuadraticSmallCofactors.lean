module

public import ArtinMatthews.SourceQuadraticShortColumns
public import ArtinMatthews.SourceQuadraticCommonIdeal
public import ArtinMatthews.SourceQuadraticGcdStrip
public import ArtinMatthews.SourceReflectionExteriorRows
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
open NumberField IsDedekindDomain QuadraticScale
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
local notation "E" => SourcePrimeExponents F S₀
local notation "q" => sourcePrimeExponentNorm F S₀

def sourceQuadraticSmallResidualColumns (cols : Finset E) (g : E) : Finset E :=
  (sourceQuadraticDivisibleColumns F S₀ cols g).image (fun b => b - g)

def sourceQuadraticSmallResidualCoeff (g : E) (u : E → ℂ) (b : E) : ℂ := u (g + b)

theorem sourceQuadraticSmall_sub_injective (cols : Finset E) (g : E) :
    Set.InjOn (fun b : E => b - g) (sourceQuadraticDivisibleColumns F S₀ cols g : Set E) := by
  intro b hb c hc he
  have hb' := ((sourceQuadratic_mem_divisibleColumns F S₀ cols g b).mp hb).2
  have hc' := ((sourceQuadratic_mem_divisibleColumns F S₀ cols g c).mp hc).2
  calc
    b = g + (b - g) := (add_tsub_cancel_of_le hb').symm
    _ = g + (c - g) := congrArg (g + ·) he
    _ = c := add_tsub_cancel_of_le hc'

theorem sourceQuadraticSmallResidualColumns_squarefree (cols : Finset E) (g : E)
    (hcols : ∀ b ∈ cols, sourceReflectionIsSquarefree b) :
    ∀ b ∈ sourceQuadraticSmallResidualColumns F S₀ cols g, sourceReflectionIsSquarefree b := by
  intro r hr
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hr
  exact sourceQuadraticExteriorQuotient_squarefree F S₀ b g
    (hcols b ((sourceQuadratic_mem_divisibleColumns F S₀ cols g b).mp hb).1)

theorem sourceQuadraticSmallResidualColumns_norm (cols : Finset E) (g : E) (P : ℝ)
    (hcols : ∀ b ∈ cols, (q b : ℝ) ≤ P) :
    ∀ b ∈ sourceQuadraticSmallResidualColumns F S₀ cols g, (q b : ℝ) ≤ P := by
  intro r hr
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hr
  have hnorm : q (b - g) ≤ q b :=
    sourceReflectionExteriorNorm_mono F S₀ (fun _ => Nat.sub_le _ _)
  have hnormR : (q (b - g) : ℝ) ≤ q b := by exact_mod_cast hnorm
  exact hnormR.trans
    (hcols b ((sourceQuadratic_mem_divisibleColumns F S₀ cols g b).mp hb).1)

theorem sourceQuadraticSmallResidualCoeff_mass (cols : Finset E) (g : E) (u : E → ℂ) :
    coeffMass (sourceQuadraticSmallResidualColumns F S₀ cols g)
      (sourceQuadraticSmallResidualCoeff F S₀ g u) ≤ coeffMass cols u := by
  unfold coeffMass sourceQuadraticSmallResidualColumns
  rw [Finset.sum_image (sourceQuadraticSmall_sub_injective F S₀ cols g)]
  have he (b : E) (hb : b ∈ sourceQuadraticDivisibleColumns F S₀ cols g) :
      sourceQuadraticSmallResidualCoeff F S₀ g u (b - g) = u b := by
    rw [sourceQuadraticSmallResidualCoeff, add_tsub_cancel_of_le
      ((sourceQuadratic_mem_divisibleColumns F S₀ cols g b).mp hb).2]
  calc
    _ = ∑ b ∈ sourceQuadraticDivisibleColumns F S₀ cols g, ‖u b‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [he b hb]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => sq_nonneg _)

theorem sourceQuadraticSmall_common_pair_reindex {A : Type*} [AddCommMonoid A]
    (cols : Finset E) (g : E) (f : E → E → A) :
    (∑ p ∈ (cols ×ˢ cols).filter (fun p : E × E => p.1 ⊓ p.2 = g), f p.1 p.2) =
      ∑ b ∈ sourceQuadraticSmallResidualColumns F S₀ cols g,
        ∑ c ∈ sourceQuadraticSmallResidualColumns F S₀ cols g,
          if Disjoint b.support c.support then f (g + b) (g + c) else 0 := by
  rw [sourceQuadratic_common_pairs_eq_divisible, Finset.sum_filter, Finset.sum_product]
  unfold sourceQuadraticSmallResidualColumns
  rw [Finset.sum_image (sourceQuadraticSmall_sub_injective F S₀ cols g)]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.sum_image (sourceQuadraticSmall_sub_injective F S₀ cols g)]
  apply Finset.sum_congr rfl
  intro c hc
  have hb' := ((sourceQuadratic_mem_divisibleColumns F S₀ cols g b).mp hb).2
  have hc' := ((sourceQuadratic_mem_divisibleColumns F S₀ cols g c).mp hc).2
  rw [add_tsub_cancel_of_le hb', add_tsub_cancel_of_le hc']

end
end ArtinMatthews.SourceEulerAssembly
