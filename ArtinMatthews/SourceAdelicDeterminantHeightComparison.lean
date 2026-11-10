module

public import ArtinMatthews.SourceKPAdelicHeight
public import ArtinMatthews.SourceKPIdeleNormOneCompact
public import ArtinMatthews.SourceAdelicHeightComparison
public import ArtinMatthews.SourceKPAdelicBorelBand
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
public import Mathlib.NumberTheory.SelbergSieve
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

/-! The actual compact determinant remainder has a uniform two-sided
effect on the full adelic Iwasawa height. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix
open scoped NumberField MatrixGroups AdeleRing
noncomputable section
variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAdelicHeight_determinant_compact_comparison :
    ∃ B : ℝ, 0 < B ∧ ∀ h ∈ (sourceKPDiagonalHom 𝔸[K]) '' sourceKPIdeleNormOneCompact K,
      ∀ g : GL (Fin 2) 𝔸[K],
        B⁻¹ * sourceKPAdelicHeight K hζ g ≤ sourceKPAdelicHeight K hζ (g * h) ∧
          sourceKPAdelicHeight K hζ (g * h) ≤ B * sourceKPAdelicHeight K hζ g :=
  sourceKPAdelicHeight_mul_uniform_on_compact K hζ _
    ((sourceKPIdeleNormOneCompact_isCompact K).image (sourceKPAdelicDiagonalMatrix_continuous K))

theorem sourceKPAdelicHeight_normOne_diagonal_comparison :
    ∃ B : ℝ, 0 < B ∧ ∀ d ∈ sourceKPIdeleNormOneCompact K,
      ∀ g : GL (Fin 2) 𝔸[K],
        B⁻¹ * sourceKPAdelicHeight K hζ g ≤
            sourceKPAdelicHeight K hζ (g * sourceKPDiagonalHom 𝔸[K] d) ∧
          sourceKPAdelicHeight K hζ (g * sourceKPDiagonalHom 𝔸[K] d) ≤
            B * sourceKPAdelicHeight K hζ g := by
  obtain ⟨B, hB, hbound⟩ := sourceKPAdelicHeight_determinant_compact_comparison K hζ
  exact ⟨B, hB, fun d hd g => hbound _ ⟨d, hd, rfl⟩ g⟩

end
end ArtinMatthews
