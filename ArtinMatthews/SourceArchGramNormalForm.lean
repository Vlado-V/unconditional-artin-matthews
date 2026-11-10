module

public import ArtinMatthews.SourceArchGramCoordinates
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import ArtinMatthews.SourceArchIwasawa
public import ArtinMatthews.SourceFiniteKPRankOneTorus
public import ArtinMatthews.SourceKPCommRingDiagonal
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

/-! The literal upper-half-space section represents every scalar-unitary orbit. -/
namespace ArtinMatthews.SourceArchJacquet
open Matrix Matrix.GeneralLinearGroup OAI.CubicEisenstein
open scoped MatrixGroups
noncomputable section

theorem sourceArchGramCoordinates_height_gram (g : GL (Fin 2) ℂ) :
    ((sourceArchGramCoordinates g).2.val : ℂ) =
      (‖(GeneralLinearGroup.det g : ℂ)‖ : ℂ) /
        (((g : Matrix (Fin 2) (Fin 2) ℂ) * star (g : Matrix (Fin 2) (Fin 2) ℂ)) 1 1) := by
  rw [← sourceArchBottomNorm_gram]
  exact Complex.ofReal_div _ _

def sourceArchPhaseUnitary (u : ℂˣ) (hu : ‖(u : ℂ)‖ = 1) :
    Matrix.unitaryGroup (Fin 2) ℂ := by
  refine ⟨(sourceGL2Diagonal u : Matrix (Fin 2) (Fin 2) ℂ),
    Matrix.mem_unitaryGroup_iff.mpr ?_⟩
  have hs : (u : ℂ) * (starRingEnd ℂ) (u : ℂ) = 1 := by
    rw [Complex.mul_conj', hu]
    norm_num
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sourceGL2Diagonal, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, hs]

theorem sourceArchPhaseUnitary_coe (u : ℂˣ) (hu : ‖(u : ℂ)‖ = 1) :
    sourceArchUnitaryGL (sourceArchPhaseUnitary u hu) = sourceGL2Diagonal u := by
  apply Units.ext
  rfl

theorem sourceArchUpperSection_scalar (z : ℂ) (y : ℝ) (hy : 0 < y) :
    (upperSection z y hy : GL (Fin 2) ℂ) * GeneralLinearGroup.scalar (Fin 2)
      (Units.mk0 (Real.sqrt y : ℂ) (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hy).ne')) =
    sourceGL2Upper z * sourceGL2Diagonal
      (Units.mk0 (y : ℂ) (Complex.ofReal_ne_zero.mpr hy.ne')) := by
  have hr : (Real.sqrt y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hy).ne'
  have hs : (Real.sqrt y : ℂ) ^ 2 = (y : ℂ) := by
    exact_mod_cast Real.sq_sqrt hy.le
  have hentry (i j : Fin 2) : (upperSection z y hy : GL (Fin 2) ℂ) i j =
      !![(Real.sqrt y : ℂ), z / (Real.sqrt y : ℂ); 0, (Real.sqrt y : ℂ)⁻¹] i j := rfl
  apply GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [sourceKPMatrix_right_scalar_entry, hentry, sourceGL2Upper,
      sourceGL2Diagonal, Matrix.mul_apply, Fin.sum_univ_two, hr]
  change (Real.sqrt y : ℂ) * (Real.sqrt y : ℂ) = (y : ℂ)
  simpa only [pow_two] using hs

theorem sourceArchBorel_gram_normal_form (b : GL (Fin 2) ℂ)
    (hb : b ∈ sourceGL2NormalizedBorel ℂ) :
    ∃ (u : ℂˣ) (k : Matrix.unitaryGroup (Fin 2) ℂ),
      b = sourceArchUpperHalfSection (sourceArchGramCoordinates b) *
        GeneralLinearGroup.scalar (Fin 2) u * sourceArchUnitaryGL k := by
  let a := GeneralLinearGroup.det b
  let y := ‖(a : ℂ)‖
  have hy : 0 < y := norm_pos_iff.mpr a.ne_zero
  let yr : ℂˣ := Units.mk0 (y : ℂ) (Complex.ofReal_ne_zero.mpr hy.ne')
  let p : ℂˣ := yr⁻¹ * a
  have hp : ‖(p : ℂ)‖ = 1 := by
    change ‖((yr⁻¹ : ℂˣ) : ℂ) * (a : ℂ)‖ = 1
    rw [norm_mul, Units.val_inv_eq_inv_val, norm_inv]
    change ‖(y : ℂ)‖⁻¹ * y = 1
    rw [Complex.norm_real, Real.norm_of_nonneg hy.le, inv_mul_cancel₀ hy.ne']
  let u : ℂˣ := Units.mk0 (Real.sqrt y : ℂ)
    (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hy).ne')
  refine ⟨u, sourceArchPhaseUnitary p hp, ?_⟩
  have hdiag : sourceGL2Diagonal a = sourceGL2Diagonal yr * sourceGL2Diagonal p := by
    change sourceGL2DiagonalHom ℂ a = sourceGL2DiagonalHom ℂ yr * sourceGL2DiagonalHom ℂ p
    rw [← map_mul]
    congr 1
    dsimp only [p]
    group
  have hc : sourceArchGramCoordinates b = (b 0 1, ⟨y, hy⟩) :=
    sourceArchGramCoordinates_borel b hb
  rw [hc, sourceArchPhaseUnitary_coe]
  change b = (upperSection (b 0 1) y hy : GL (Fin 2) ℂ) *
    GeneralLinearGroup.scalar (Fin 2) u * sourceGL2Diagonal p
  calc
    b = sourceGL2Upper (b 0 1) * sourceGL2Diagonal a :=
      sourceGL2NormalizedBorel_factor ℂ b hb
    _ = (sourceGL2Upper (b 0 1) * sourceGL2Diagonal yr) * sourceGL2Diagonal p := by
      rw [hdiag, mul_assoc]
    _ = _ := by rw [sourceArchUpperSection_scalar]

theorem sourceArch_gram_normal_form (g : GL (Fin 2) ℂ) :
    ∃ (u : ℂˣ) (k : Matrix.unitaryGroup (Fin 2) ℂ),
      g = sourceArchUpperHalfSection (sourceArchGramCoordinates g) *
        GeneralLinearGroup.scalar (Fin 2) u * sourceArchUnitaryGL k := by
  let b := sourceArchIwasawaBorel g
  let d := sourceArchIwasawaScalar g
  let k₀ := sourceArchIwasawaUnitary g
  have hc : sourceArchGramCoordinates g = sourceArchGramCoordinates b := by
    rw [sourceArchIwasawa_factor g, sourceArchGramCoordinates_unitary,
      sourceArchGramCoordinates_scalar]
  obtain ⟨u, k, hk⟩ := sourceArchBorel_gram_normal_form b (sourceArchIwasawaBorel_mem g)
  refine ⟨u*d, k*k₀, ?_⟩
  calc
    g = b * GeneralLinearGroup.scalar (Fin 2) d * sourceArchUnitaryGL k₀ :=
      sourceArchIwasawa_factor g
    _ = (sourceArchUpperHalfSection (sourceArchGramCoordinates g) *
        GeneralLinearGroup.scalar (Fin 2) u * sourceArchUnitaryGL k) *
        GeneralLinearGroup.scalar (Fin 2) d * sourceArchUnitaryGL k₀ := by rw [hk, ← hc]
    _ = sourceArchUpperHalfSection (sourceArchGramCoordinates g) *
        (GeneralLinearGroup.scalar (Fin 2) u *
          (sourceArchUnitaryGL k * GeneralLinearGroup.scalar (Fin 2) d)) *
          sourceArchUnitaryGL k₀ := by group
    _ = sourceArchUpperHalfSection (sourceArchGramCoordinates g) *
        (GeneralLinearGroup.scalar (Fin 2) u *
          (GeneralLinearGroup.scalar (Fin 2) d * sourceArchUnitaryGL k)) *
          sourceArchUnitaryGL k₀ := by rw [← GeneralLinearGroup.scalar_commute d]
    _ = _ := by rw [map_mul, map_mul]; group

end
end ArtinMatthews.SourceArchJacquet
