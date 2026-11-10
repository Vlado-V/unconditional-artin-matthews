module

public import ArtinMatthews.SourceKPAdelicHeight
public import ArtinMatthews.SourceKPAdelicCompactIntersection
public import ArtinMatthews.SourceKPAdelicTranslatedHeight
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

/-! Cusp separation from the lower row of the actual adelic matrix.
Every finite place occurs in the product, including places above six. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open SourceArchJacquet
open scoped NumberField MatrixGroups AdeleRing BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAdelicHeight_lowerLeft_bound (g : GL (Fin 2) 𝔸[K])
    (u : IdeleGroup (𝓞 K) K) (hu : g 1 0 = (u : 𝔸[K])) :
    sourceKPAdelicHeight K hζ g ≤
      sourceKPIdeleAbsoluteNorm K (GeneralLinearGroup.det g / u ^ 2) := by
  let d := GeneralLinearGroup.det g / u ^ 2
  let I := fun v : InfinitePlace K => sourceArchHeight (sourceKPAdelicBaseComplexAt K hζ v g)
  let F := fun P : HeightOneSpectrum (𝓞 K) =>
    sourceKPFiniteMatrixHeight K P (sourceKPAdelicBaseFiniteAt K P g)
  let DI := fun v : InfinitePlace K =>
    ‖(sourceKPIdeleInfiniteCoordinate K v d : v.Completion)‖
  let DF := fun P : HeightOneSpectrum (𝓞 K) =>
    ‖(sourceKPIdeleFiniteCoordinate K P d : P.adicCompletion K)‖
  have hI (v : InfinitePlace K) : I v ≤ DI v := by
    let gv := sourceKPAdelicBaseComplexAt K hζ v g
    let uv := sourceKPArchComplexEquiv K hζ v
      (sourceKPIdeleInfiniteCoordinate K v u : v.Completion)
    have huv : gv 1 0 = uv := by
      change sourceKPArchComplexEquiv K hζ v ((g 1 0).1 v) = _
      rw [hu]
      rfl
    have hu0 : 0 < ‖uv‖ := by
      apply norm_pos_iff.mpr
      simpa only [map_zero] using (sourceKPArchComplexEquiv K hζ v).injective.ne
        (sourceKPIdeleInfiniteCoordinate K v u).ne_zero
    have hden : ‖uv‖ ^ 2 ≤ sourceArchBottomNorm gv := by
      rw [sourceArchBottomNorm, huv]
      exact le_add_of_nonneg_right (sq_nonneg _)
    have hbound : sourceArchHeight gv ≤
        ‖(GeneralLinearGroup.det gv : ℂ)‖ / ‖uv‖ ^ 2 := by
      exact div_le_div_of_nonneg_left (norm_nonneg _) (sq_pos_of_pos hu0) hden
    have hval : DI v = ‖(GeneralLinearGroup.det gv : ℂ)‖ / ‖uv‖ ^ 2 := by
      dsimp only [DI, d]
      rw [map_div, map_pow, Units.val_div_eq_div_val, Units.val_pow_eq_pow_val,
        norm_div, norm_pow, ← sourceKPArchComplexEquiv_norm K hζ v,
        sourceKPAdelicComplexCoordinate_det]
      rw [← sourceKPArchComplexEquiv_norm K hζ v
        (sourceKPIdeleInfiniteCoordinate K v u : v.Completion)]
    exact hval ▸ hbound
  have hF (P : HeightOneSpectrum (𝓞 K)) : F P ≤ DF P := by
    let gP := sourceKPAdelicBaseFiniteAt K P g
    let uP := sourceKPIdeleFiniteCoordinate K P u
    have huP : gP 1 0 = (uP : P.adicCompletion K) := by
      change (g 1 0).2 P = _
      rw [hu]
      rfl
    have hu0 : 0 < ‖(uP : P.adicCompletion K)‖ := norm_pos_iff.mpr uP.ne_zero
    have hden : ‖(uP : P.adicCompletion K)‖ ^ 2 ≤ sourceKPBottomMax gP ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (by rw [← huP]; exact le_max_left _ _) _
    have hbound : sourceKPFiniteMatrixHeight K P gP ≤
        ‖(GeneralLinearGroup.det gP : P.adicCompletion K)‖ /
          ‖(uP : P.adicCompletion K)‖ ^ 2 := by
      exact div_le_div_of_nonneg_left (norm_nonneg _) (sq_pos_of_pos hu0) hden
    have hval : DF P = ‖(GeneralLinearGroup.det gP : P.adicCompletion K)‖ /
        ‖(uP : P.adicCompletion K)‖ ^ 2 := by
      dsimp only [DF, d]
      rw [map_div, map_pow, Units.val_div_eq_div_val, Units.val_pow_eq_pow_val,
        norm_div, norm_pow, sourceKPAdelicFiniteCoordinate_det]
    exact hval ▸ hbound
  have hIs : (∏ v, I v ^ v.mult) ≤ ∏ v, DI v ^ v.mult := by
    apply Finset.prod_le_prod₀
    · intro v _
      exact pow_nonneg (sourceArchHeight_pos _).le _
    · intro v _
      exact pow_le_pow_left₀ (sourceArchHeight_pos _).le (hI v) _
  have hFs : F.HasFiniteMulSupport := sourceKPAdelicFiniteHeight_finite_support K g
  have hDFs : DF.HasFiniteMulSupport :=
    FiniteAdeleRing.hasFiniteMulSupport_norm (sourceKPIdeleFiniteUnit K d)
  have hFs_le : (∏ᶠ P, F P) ≤ ∏ᶠ P, DF P :=
    finprod_le_finprod₀ hFs (fun P => (sourceKPFiniteMatrixHeight_pos K P _).le) hDFs hF
  have hF0 : 0 ≤ ∏ᶠ P, F P := by
    rw [finprod_eq_prod _ hFs]
    exact Finset.prod_nonneg (fun P _ => (sourceKPFiniteMatrixHeight_pos K P _).le)
  have hDI0 : 0 ≤ ∏ v, DI v ^ v.mult :=
    Finset.prod_nonneg (fun v _ => pow_nonneg (norm_nonneg _) _)
  calc
    sourceKPAdelicHeight K hζ g = (∏ v, I v ^ v.mult) * ∏ᶠ P, F P := by
      simpa only [I, F, sourceKPFiniteMatrixHeight, sourceKPBottomMax] using
        sourceKPAdelicHeight_product K hζ g
    _ ≤ (∏ v, DI v ^ v.mult) * ∏ᶠ P, DF P := mul_le_mul hIs hFs_le hF0 hDI0
    _ = sourceKPIdeleAbsoluteNorm K d := by
      change _ = ‖(sourceKPIdeleInfiniteUnit K d : InfiniteAdeleRing K)‖ *
        ‖(sourceKPIdeleFiniteUnit K d : 𝔸ᶠ[K])‖
      rw [InfiniteAdeleRing.norm_def, FiniteAdeleRing.norm_eq_finprod_of_unit]
      rfl

end
end ArtinMatthews
