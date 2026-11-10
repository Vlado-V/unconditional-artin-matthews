module

public import ArtinMatthews.SourceKPAdelicTranslatedHeight
public import ArtinMatthews.SourceKPAdelicCompactSection
public import ArtinMatthews.SourceKPAdelicSectionBound
public import ArtinMatthews.SourceKPAdelicUpperProjection
public import ArtinMatthews.SourceKPRationalHeightComplex
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

/-! Absolute convergence of the actual compact-section Eisenstein sum
in an explicit right half-plane over the given number field. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open scoped NumberField MatrixGroups AdeleRing BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAdelicOpenCell_projection (q : SourceKPAdelicProjective K hζ)
    (g : GL (Fin 2) 𝔸[K]) (hp : sourceKPAdelicProjectiveProjection K hζ q = ProjGenLinGroup.mk g)
    (x : K) :
    sourceKPAdelicProjectiveProjection K hζ (sourceKPAdelicProjectiveWeyl K hζ *
      sourceKPAdelicUpperLift K hζ (algebraMap K 𝔸[K] x) * q) =
        ProjGenLinGroup.mk (sourceKPAdelicOpenCellMatrix K x * g) := by
  have hw : sourceKPAdelicProjectiveProjection K hζ (sourceKPAdelicProjectiveWeyl K hζ) =
      ProjGenLinGroup.mk (sourceKPWeylMatrix 𝔸[K]) := by
    rw [sourceKPAdelicProjectiveWeyl, sourceKPAdelicProjectiveRationalLift_projection,
      ProjGenLinGroup.map_mk, sourceKPWeylMatrix_map]
  rw [map_mul, map_mul, hw, sourceKPAdelicUpperLift_projection, hp, ← map_mul, ← map_mul]
  rfl

theorem sourceKPAdelicCompact_openCell_bound {s : ℂ}
    (hs : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (q : SourceKPAdelicProjective K hζ) (g : GL (Fin 2) 𝔸[K])
    (hp : sourceKPAdelicProjectiveProjection K hζ q = ProjGenLinGroup.mk g) (x : K) :
    ‖sourceKPAdelicCompactScalar K hζ s (sourceKPAdelicProjectiveWeyl K hζ *
      sourceKPAdelicUpperLift K hζ (algebraMap K 𝔸[K] x) * q)‖ ≤
        (sourceKPAdelicHeightConstant K hζ g) ^ (s.re+1/2) *
          Height.mulHeight₁ x ^ (-(2*s.re+1)) := by
  have hr : 0 ≤ s.re+1/2 := by
    have hn : 0 ≤ ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hx := Height.mulHeight₁_pos x
  have hc := sourceKPAdelicHeightConstant_pos K hζ g
  have hpow : ((Height.mulHeight₁ x)⁻¹ ^ 2) ^ (s.re+1/2) =
      Height.mulHeight₁ x ^ (-(2*s.re+1)) := by
    calc
      _ = (Height.mulHeight₁ x ^ (-2 : ℝ)) ^ (s.re+1/2) := by
        rw [Real.rpow_neg hx.le, Real.rpow_two, inv_pow]
      _ = Height.mulHeight₁ x ^ ((-2 : ℝ)*(s.re+1/2)) :=
        (Real.rpow_mul hx.le _ _).symm
      _ = _ := by congr 1; ring
  calc
    _ ≤ (sourceKPAdelicHeight K hζ (sourceKPAdelicOpenCellMatrix K x*g)) ^ (s.re+1/2) :=
      sourceKPAdelicCompactScalar_height_bound K hζ s _ _ (sourceKPAdelicOpenCell_projection K hζ q g hp x)
    _ ≤ (sourceKPAdelicHeightConstant K hζ g * (Height.mulHeight₁ x)⁻¹ ^ 2) ^ (s.re+1/2) :=
      Real.rpow_le_rpow (sourceKPAdelicHeight_pos K hζ _).le
        (sourceKPAdelicHeight_translate K hζ g x) hr
    _ = _ := by rw [Real.mul_rpow hc.le (sq_nonneg _), hpow]

theorem sourceKPAdelicCompact_openCell_summable {s : ℂ}
    (hs : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (q : SourceKPAdelicProjective K hζ) :
    Summable (fun x : K => sourceKPAdelicCompactScalar K hζ s
      (sourceKPAdelicProjectiveWeyl K hζ * sourceKPAdelicUpperLift K hζ (algebraMap K 𝔸[K] x) * q)) := by
  obtain ⟨g,hg⟩ := ProjGenLinGroup.mk_surjective (sourceKPAdelicProjectiveProjection K hζ q)
  apply Summable.of_norm
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (sourceKPAdelicCompact_openCell_bound K hζ hs q g hg.symm)
    ((sourceKPRationalHeight_rpow_summable K hs).mul_left
      ((sourceKPAdelicHeightConstant K hζ g) ^ (s.re+1/2)))

theorem sourceKPAdelicCompactEisenstein_converges {s : ℂ}
    (hs : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (q : SourceKPAdelicProjective K hζ) :
    sourceKPAdelicEisensteinConverges K hζ s (sourceKPAdelicCompactSection K hζ s) q := by
  let f := sourceKPAdelicPrincipalSeriesScalar K hζ s (sourceKPAdelicCompactSection K hζ s)
  let u : Option K → ℂ := fun t => sourceKPAdelicRationalSummand K hζ f q
    (sourceKPRationalBorelCosetEquiv K t)
  have hsome : Summable (fun x : K => u (some x)) := by
    have he (x : K) : u (some x) = sourceKPAdelicCompactScalar K hζ s
        (sourceKPAdelicProjectiveWeyl K hζ * sourceKPAdelicUpperLift K hζ (algebraMap K 𝔸[K] x) * q) := by
      change f.val (sourceKPAdelicProjectiveRationalLift K hζ
        (ProjGenLinGroup.mk (sourceGL2Weyl * sourceGL2Upper x)) * q) = _
      rw [sourceKPAdelicUpperLift_rational, sourceKPAdelicProjectiveWeyl, sourceKPWeylMatrix_field,
        map_mul, map_mul]
      rfl
    simp_rw [he]
    exact sourceKPAdelicCompact_openCell_summable K hζ hs q
  let e : Option K ≃ K ⊕ PUnit.{1} := Equiv.optionEquivSumPUnit K
  have hsum : Summable (fun t : K ⊕ PUnit.{1} => u (e.symm t)) := by
    apply Summable.sum
    · simpa only [Function.comp_def, e, Equiv.optionEquivSumPUnit_symm_inl] using hsome
    · exact (hasSum_fintype _).summable
  have hu : Summable u := e.symm.summable_iff.mp hsum
  exact (sourceKPRationalBorelCosetEquiv K).summable_iff.mp hu

theorem sourceKPAdelicCompactEisenstein_weyl {s : ℂ}
    (hs : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (q : SourceKPAdelicProjective K hζ) :
    sourceKPAdelicEisensteinSum K hζ s (sourceKPAdelicCompactSection K hζ s)
      (sourceKPAdelicProjectiveWeyl K hζ*q) =
        sourceKPAdelicEisensteinSum K hζ s (sourceKPAdelicCompactSection K hζ s) q :=
  sourceKPAdelicEisensteinSum_weyl K hζ s _ q (sourceKPAdelicCompactEisenstein_converges K hζ hs q)

end
end ArtinMatthews
