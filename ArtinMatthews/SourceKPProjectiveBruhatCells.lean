module

public import ArtinMatthews.SourceFiniteKPProjectiveBorel
public import ArtinMatthews.SourceKPAdeleWeylCoordinates
public import ArtinMatthews.SourceKPCompactDiagonal
public import ArtinMatthews.SourceKPCompactWeyl
public import ArtinMatthews.SourceKPProjectiveCanonicalFactors
public import ArtinMatthews.SourceKPProjectiveSections
public import ArtinMatthews.SourceKubotaBottomRows
public import ArtinMatthews.SourceKubotaGL2Generation
public import ArtinMatthews.SourceKubotaMultipliers
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

/-! The actual closed and open Bruhat cells of the local projective
cubic cover. The genuine Weyl lift squares to one and the normalized
Borel absorbs the exact central phase on either cell. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open scoped NumberField MatrixGroups
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K))

theorem sourceFiniteKP2ProjectiveLift_one :
    sourceFiniteKP2ProjectiveLift K hζ P 1 = 1 := (sourceFiniteKP2ProjectiveMk K hζ P).map_one

theorem sourceFiniteKP2ProjectiveLift_upper_zero :
    sourceFiniteKP2ProjectiveLift K hζ P (sourceGL2Upper (0 : P.adicCompletion K)) = 1 := by
  rw [sourceGL2Upper_zero, sourceFiniteKP2ProjectiveLift_one]

theorem sourceFiniteKP2ProjectiveLift_weyl_square :
    sourceFiniteKP2ProjectiveLift K hζ P sourceGL2Weyl *
      sourceFiniteKP2ProjectiveLift K hζ P sourceGL2Weyl = 1 := by
  let W : GL (Fin 2) (P.adicCompletion K) := sourceGL2Weyl
  have hw : W * W = 1 := by
    rw [show W = sourceKPWeylMatrix (P.adicCompletion K) from (sourceKPWeylMatrix_field _).symm]
    exact sourceKPWeylMatrix_square _
  have hs : sourceFiniteKP2Multiplier K hζ P W W = 1 := by
    change sourceKP2Multiplier (sourceFiniteKPHilbert K hζ P) W sourceGL2Weyl = 1
    rw [sourceKP2Multiplier_right_weyl_formula _ (sourceFiniteKPHilbert_minus_right K hζ P),
      hw, sourceKubotaX_one, show sourceKubotaX W = 1 from sourceKubotaX_weyl,
      div_one, map_one, MonoidHom.one_apply]
  rw [sourceFiniteKP2ProjectiveLift_mul_of_phase_one K hζ P W W hs, hw, sourceFiniteKP2ProjectiveLift_one]

theorem sourceFiniteKPProjectiveBorel_of_triangular (g : SourceFiniteKP2Cover K hζ P)
    (hc : g.base 1 0 = 0) :
    ∃ b : SourceFiniteKPProjectiveBorel K hζ P, b.val = sourceFiniteKP2ProjectiveMk K hζ P g := by
  let d := Units.mk0 (g.base 1 1) (sourceGL2_bottom_right_ne_zero g.base hc)
  let a := g * sourceFiniteKP2Scalar K hζ P d⁻¹
  have ha : a ∈ sourceFiniteKPNormalizedBorelSubgroup K hζ P := by
    change (g.base * GeneralLinearGroup.scalar (Fin 2) d⁻¹) 1 0 = 0 ∧
      (g.base * GeneralLinearGroup.scalar (Fin 2) d⁻¹) 1 1 = 1
    rw [sourceGL2_right_scalar_apply, sourceGL2_right_scalar_apply, hc, zero_mul]
    exact ⟨rfl, d.val_inv⟩
  refine ⟨sourceFiniteKPProjectiveBorelEquiv K hζ P ⟨a, ha⟩, ?_⟩
  rw [sourceFiniteKPProjectiveBorelEquiv_val]
  change sourceFiniteKP2ProjectiveMk K hζ P (g * sourceFiniteKP2Scalar K hζ P d⁻¹) = _
  rw [map_mul, sourceFiniteKP2ProjectiveMk_scalar, mul_one]

theorem sourceFiniteKP2Projective_bruhat_cells (g : SourceFiniteKP2Projective K hζ P) :
    (∃ b : SourceFiniteKPProjectiveBorel K hζ P, g = b.val) ∨
      ∃ (b : SourceFiniteKPProjectiveBorel K hζ P) (t : P.adicCompletion K),
        g = b.val * sourceFiniteKP2ProjectiveLift K hζ P sourceGL2Weyl *
          sourceFiniteKP2ProjectiveLift K hζ P (sourceGL2Upper t) := by
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (sourceFiniteKP2Scalar K hζ P).range g
  change sourceFiniteKP2ProjectiveMk K hζ P x = g at hx
  by_cases hc : x.base 1 0 = 0
  · obtain ⟨b, hb⟩ := sourceFiniteKPProjectiveBorel_of_triangular K hζ P x hc
    exact Or.inl ⟨b, hx.symm.trans hb.symm⟩
  · let t := x.base 1 1 / x.base 1 0
    let y := x * sourceFiniteKP2Lift K hζ P (sourceGL2Upper (-t)) * sourceFiniteKP2Lift K hζ P sourceGL2Weyl
    have hy : y.base 1 0 = 0 := by
      change ((x.base * sourceGL2Upper (-t) * sourceGL2Weyl : GL (Fin 2) (P.adicCompletion K)) :
        Matrix (Fin 2) (Fin 2) (P.adicCompletion K)) 1 0 = 0
      rw [sourceGL2_right_weyl_bottom_left, sourceGL2_right_upper_bottom_right]
      dsimp only [t]
      rw [mul_neg, ← mul_div_assoc, mul_div_cancel_left₀ _ hc, neg_add_cancel]
    obtain ⟨b, hb⟩ := sourceFiniteKPProjectiveBorel_of_triangular K hζ P y hy
    right
    refine ⟨b, t, ?_⟩
    rw [hb]
    let m := sourceFiniteKP2ProjectiveMk K hζ P
    let l := sourceFiniteKP2ProjectiveLift K hζ P
    change g = m (x * sourceFiniteKP2Lift K hζ P (sourceGL2Upper (-t)) *
      sourceFiniteKP2Lift K hζ P sourceGL2Weyl) * l sourceGL2Weyl * l (sourceGL2Upper t)
    rw [map_mul m, map_mul m]
    change g = m x * l (sourceGL2Upper (-t)) * l sourceGL2Weyl * l sourceGL2Weyl * l (sourceGL2Upper t)
    have hN : l (sourceGL2Upper (-t)) * l (sourceGL2Upper t) = 1 := by
      rw [sourceFiniteKP2ProjectiveLift_upper_add, neg_add_cancel, sourceFiniteKP2ProjectiveLift_upper_zero]
    rw [mul_assoc (m x * l (sourceGL2Upper (-t))), sourceFiniteKP2ProjectiveLift_weyl_square,
      mul_one, mul_assoc, hN, mul_one, hx]

end
end ArtinMatthews
