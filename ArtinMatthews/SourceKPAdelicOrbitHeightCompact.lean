module

public import ArtinMatthews.SourceKPAdelicOrbitHeight
public import ArtinMatthews.SourceKPAdelicHeightCompact
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

/-! Uniform bounds for the actual rational-orbit height over compact
adelic matrix sets, independent of the lift to the cubic cover. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAdelicHeight_le_weyl_constant (g : GL (Fin 2) 𝔸[K]) :
    sourceKPAdelicHeight K hζ g ≤
      sourceKPAdelicHeightConstant K hζ (sourceKPWeylMatrix 𝔸[K]*g) := by
  have h := sourceKPAdelicHeight_translate K hζ (sourceKPWeylMatrix 𝔸[K]*g) (0 : K)
  simpa only [sourceKPAdelicOpenCellMatrix, map_zero, sourceKPUpperMatrix_zero, mul_one,
    ← mul_assoc, sourceKPWeylMatrix_square, one_mul, Height.mulHeight₁_zero, inv_one,
    one_pow] using h

theorem sourceKPAdelicOrbitHeight_bounded_on_matrices
    (S : Set (GL (Fin 2) 𝔸[K])) (hS : IsCompact S) :
    ∃ B : ℝ, 0 < B ∧ ∀ g ∈ S, ∀ q : SourceKPAdelicProjective K hζ,
      sourceKPAdelicProjectiveProjection K hζ q = ProjGenLinGroup.mk g →
        sourceKPAdelicOrbitHeight K hζ q ≤ B := by
  obtain ⟨B₁,hB₁,h₁⟩ := sourceKPAdelicHeightConstant_bounded K hζ S hS
  have hW : IsCompact ((fun g : GL (Fin 2) 𝔸[K] => sourceKPWeylMatrix 𝔸[K]*g) '' S) :=
    hS.image (continuous_const.mul continuous_id)
  obtain ⟨B₂,_hB₂,h₂⟩ := sourceKPAdelicHeightConstant_bounded K hζ _ hW
  refine ⟨max B₁ B₂, lt_of_lt_of_le hB₁ (le_max_left _ _), ?_⟩
  intro g hg q hq
  apply (sourceKPAdelicOrbitHeight_le K hζ q g hq).trans
  apply max_le
  · exact (sourceKPAdelicHeight_le_weyl_constant K hζ g).trans
      ((h₂ _ ⟨g,hg,rfl⟩).trans (le_max_right _ _))
  · exact (h₁ g hg).trans (le_max_left _ _)

end
end ArtinMatthews
