module

public import ArtinMatthews.SpectralPoincareGeometricKernel
public import ArtinMatthews.AtkinLehnerMixedPhase
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Literal Bruhat decomposition of the actual nonzero-modulus matrices and
the corresponding invariant-measure change of variable for compact tests. -/

noncomputable section
open Matrix Set MeasureTheory Filter
open scoped MatrixGroups InnerProductSpace

namespace ArtinMatthews

def realWeylMatrix (c : ℝ) (hc : c ≠ 0) : SL(2, ℝ) :=
  ⟨!![0,-c⁻¹;c,0],by simp [Matrix.det_fin_two,hc]⟩

theorem realTranslation_zero : realTranslation 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem atkinRealMap_smul (M : SL(2, ℤ)) (z : UpperHalfPlane) :
    atkinRealMap M • z = M • z := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_specialLinearGroup_apply,UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [atkinRealMap]

set_option backward.isDefEq.respectTransparency false in
theorem integer_matrix_bruhat (M : SL(2, ℤ)) {c : ℤ} (hc : c ≠ 0) (hM : M 1 0 = c) :
    atkinRealMap M =
      realTranslation ((M 0 0 : ℝ) / c) *
        realWeylMatrix (c : ℝ) (by exact_mod_cast hc) *
          realTranslation ((M 1 1 : ℝ) / c) := by
  have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  have hd : (M 0 0 : ℝ) * (M 1 1 : ℝ) - (M 0 1 : ℝ) * c = 1 := by
    have h := M.prop
    rw [Matrix.det_fin_two,hM] at h
    exact_mod_cast h
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [atkinRealMap,realTranslation,realWeylMatrix,Matrix.SpecialLinearGroup.coe_mul,
    Matrix.mul_apply,Fin.sum_univ_two,hM]
  all_goals field_simp [hcR]
  all_goals nlinarith [hd]

theorem realTranslation_measurePreserving (x : ℝ) :
    MeasurePreserving (fun z : UpperHalfPlane => realTranslation x • z) volume volume := by
  change MeasurePreserving
    (fun z : UpperHalfPlane => Matrix.SpecialLinearGroup.mapGL ℝ (realTranslation x) • z) _ _
  exact measurePreserving_smul _ _

def compactBruhatWindowKernel (ψ φ : h2SmoothCompactSeeds) (c : ℝ) (hc : c ≠ 0)
    (α β : ℝ) : ℂ :=
  ∫ z : UpperHalfPlane,
    inner ℂ (ψ.val (realTranslation (-β) • z))
      (φ.val (realTranslation α • (realWeylMatrix c hc • z)))

theorem compactPoincareGeometricKernel_bruhat (ψ φ : h2SmoothCompactSeeds)
    (M : SL(2, ℤ)) {c : ℤ} (hc : c ≠ 0) (hM : M 1 0 = c) :
    compactPoincareGeometricKernel ψ φ M =
      compactBruhatWindowKernel ψ φ (c : ℝ) (by exact_mod_cast hc)
        ((M 0 0 : ℝ) / c) ((M 1 1 : ℝ) / c) := by
  let α : ℝ := (M 0 0 : ℝ) / c
  let β : ℝ := (M 1 1 : ℝ) / c
  have he := (realTranslation_measurePreserving (-β)).integral_comp
    (show MeasurableEmbedding (fun z : UpperHalfPlane => realTranslation (-β) • z) from
      measurableEmbedding_const_smul (realTranslation (-β)))
    (fun z : UpperHalfPlane => inner ℂ (ψ.val z) (φ.val (M • z)))
  change (∫ z : UpperHalfPlane, inner ℂ (ψ.val z) (φ.val (M • z))) = _
  rw [← he]
  apply integral_congr_ae
  filter_upwards [] with z
  have hact : M • (realTranslation (-β) • z) =
      realTranslation α • (realWeylMatrix (c : ℝ) (by exact_mod_cast hc) • z) := by
    rw [← atkinRealMap_smul,integer_matrix_bruhat M hc hM]
    change (realTranslation α * realWeylMatrix (c : ℝ) (by exact_mod_cast hc) * realTranslation β) •
      (realTranslation (-β) • z) = _
    rw [mul_smul,mul_smul,← mul_smul (realTranslation β),realTranslation_mul,
      add_neg_cancel,realTranslation_zero,one_smul]
  rw [hact]

end ArtinMatthews
