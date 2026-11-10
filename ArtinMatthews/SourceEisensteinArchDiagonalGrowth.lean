module

public import ArtinMatthews.SourceArchOnlyIdele
public import ArtinMatthews.SourceKPAdelicEisensteinHolomorphic
public import ArtinMatthews.SourceCuspAdelicHeightGrowth
public import ArtinMatthews.SourceEisensteinHeightMajorant
public import ArtinMatthews.SourceKPAdelicHeightCompact
public import ArtinMatthews.SourceKPAdelicOrbitHeightCompact
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

/-! Uniform polynomial growth along every expanding archimedean diagonal, including the balanced cusp flow. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix
open scoped NumberField MatrixGroups AdeleRing BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAdelicCompactEisenstein_archDiagonal_growth {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2 * s.re + 1)
    (S : Set (GL (Fin 2) 𝔸[K])) (hS : IsCompact S) :
    ∃ C : ℝ, 0 < C ∧ ∀ g ∈ S, ∀ a : (InfiniteAdeleRing K)ˣ,
      (∀ v, 1 ≤ ‖(a : InfiniteAdeleRing K) v‖) → ∀ q : SourceKPAdelicProjective K hζ,
      sourceKPAdelicProjectiveProjection K hζ q =
          ProjGenLinGroup.mk (g * sourceKPDiagonalHom 𝔸[K] (sourceArchOnlyIdele K a)) →
      ‖sourceKPAdelicCompactEisenstein K hζ s q‖ ≤ C * ‖(a : InfiniteAdeleRing K)‖ ^ (s.re + 1 / 2) := by
  obtain ⟨B₁, hB₁, hbound₁⟩ := sourceKPAdelicHeightConstant_bounded K hζ S hS
  have hSW : IsCompact ((fun g : GL (Fin 2) 𝔸[K] => sourceKPWeylMatrix 𝔸[K] * g) '' S) :=
    hS.image (continuous_const.mul continuous_id)
  obtain ⟨B₂, _hB₂, hbound₂⟩ := sourceKPAdelicHeightConstant_bounded K hζ _ hSW
  let B := max B₁ B₂
  let Z := ∑' x : K, Height.mulHeight₁ x ^ (-(2 * s.re + 1))
  have hB : 0 < B := hB₁.trans_le (le_max_left _ _)
  have hZ : 0 ≤ Z := tsum_nonneg (fun x => Real.rpow_nonneg (Height.mulHeight₁_nonneg x) _)
  refine ⟨B ^ (s.re + 1 / 2) * (1 + Z), mul_pos (Real.rpow_pos_of_pos hB _) (by linarith), ?_⟩
  intro g hg a ha q hq
  let N := ‖(a : InfiniteAdeleRing K)‖
  have hN : 0 < N := by
    change 0 < ‖(a : InfiniteAdeleRing K)‖
    rw [← sourceArchOnlyIdele_norm K]
    exact sourceKPIdeleAbsoluteNorm_pos K _
  let D := sourceKPDiagonalHom 𝔸[K] (sourceArchOnlyIdele K a)
  have hC : sourceKPAdelicHeightConstant K hζ (g * D) ≤ N * B :=
    (sourceKPAdelicHeightConstant_right_archOnly K hζ g a ha).trans
      (mul_le_mul_of_nonneg_left ((hbound₁ g hg).trans (le_max_left _ _)) hN.le)
  have hH : sourceKPAdelicHeight K hζ (g * D) ≤ N * B := by
    apply (sourceKPAdelicHeight_le_weyl_constant K hζ (g * D)).trans
    rw [← mul_assoc]
    exact (sourceKPAdelicHeightConstant_right_archOnly K hζ (sourceKPWeylMatrix 𝔸[K] * g) a ha).trans
      (mul_le_mul_of_nonneg_left ((hbound₂ _ ⟨g, hg, rfl⟩).trans (le_max_right _ _)) hN.le)
  apply (sourceKPAdelicCompactEisenstein_uniform_height_majorant K hζ hs q (g * D) hq (N * B) hH hC).trans_eq
  rw [Real.mul_rpow hN.le hB.le]
  change N ^ (s.re + 1 / 2) * B ^ (s.re + 1 / 2) * (1 + Z) = _
  ring

end
end ArtinMatthews
