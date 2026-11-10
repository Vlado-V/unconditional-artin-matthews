module

public import ArtinMatthews.SourceArchGramCoordinates
public import OAI.NumberTheory.DirichletL.QuadraticSieve.SelectedExponents
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

/-! The actual Gram upper coordinates agree with the checked SL2 hyperbolic model. -/
namespace ArtinMatthews.SourceArchJacquet
open Matrix Matrix.GeneralLinearGroup OAI.CubicEisenstein
open scoped MatrixGroups
noncomputable section

def sourceArchUpperCoordinatesHomeomorph : SourceArchUpperHalfSpace ≃ₜ UpperCoordinates where
  toFun p := ⟨(p.1, p.2.val), p.2.property⟩
  invFun p := (p.val.1, ⟨p.val.2, p.property⟩)
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).subtype_mk _
  continuous_invFun := (continuous_fst.comp continuous_subtype_val).prodMk
    ((continuous_snd.comp continuous_subtype_val).subtype_mk _)

def sourceArchHyperbolicHomeomorph : SourceArchUpperHalfSpace ≃ₜ HyperbolicSpace :=
  sourceArchUpperCoordinatesHomeomorph.trans upperCoordinatesHomeomorph

lemma sourceArchHyperbolicHomeomorph_apply (p : SourceArchUpperHalfSpace) :
    sourceArchHyperbolicHomeomorph p = upperPoint p.1 p.2.val p.2.property := rfl

lemma sourceArchHeight_specialLinear (m : SL(2, ℂ)) :
    sourceArchHeight (m : GL (Fin 2) ℂ) = liftedHeight m := by
  simp only [sourceArchHeight, SpecialLinearGroup.coeToGL_det, Units.val_one, norm_one,
    one_div, liftedHeight, rowEnergy, complexBottomRow, sourceArchBottomNorm]
  rfl

lemma sourceArchGramShift_specialLinear (m : SL(2, ℂ)) :
    sourceArchGramShift (m : GL (Fin 2) ℂ) = matrixHorizontal m := rfl

lemma sourceArchHyperbolicHomeomorph_gram_specialLinear (m : SL(2, ℂ)) :
    sourceArchHyperbolicHomeomorph (sourceArchGramCoordinates (m : GL (Fin 2) ℂ)) =
      (m : HyperbolicSpace) := by
  rw [sourceArchHyperbolicHomeomorph_apply, matrix_point_coordinates m]
  apply upperPoint_congr
  · exact sourceArchGramShift_specialLinear m
  · exact sourceArchHeight_specialLinear m

lemma sourceArchHyperbolicHomeomorph_specialLinear_action (m : SL(2, ℂ))
    (p : SourceArchUpperHalfSpace) :
    sourceArchHyperbolicHomeomorph
      (sourceArchGramCoordinates ((m : GL (Fin 2) ℂ) * sourceArchUpperHalfSection p)) =
      m • sourceArchHyperbolicHomeomorph p := by
  change sourceArchHyperbolicHomeomorph
    (sourceArchGramCoordinates ((m * upperSection p.1 p.2.val p.2.property : SL(2, ℂ)) : GL (Fin 2) ℂ)) = _
  rw [sourceArchHyperbolicHomeomorph_gram_specialLinear]
  rfl

end
end ArtinMatthews.SourceArchJacquet
