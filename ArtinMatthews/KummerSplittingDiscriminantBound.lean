module

public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Int.Star
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleRing.Principal
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

/-! General integral-basis discriminant bounds, extracted from the first
four arithmetic results of OAI PrimePackets.DiscriminantBounds. The proofs
use Mathlib only and are independent of any analytic counting theorem. -/

noncomputable section
namespace ArtinMatthews.KummerDiscriminant

open Module Matrix NumberField Complex
open scoped BigOperators NumberField

lemma integralBasis_discriminant_index {K I : Type*} [Field K] [NumberField K]
    [Fintype I] [DecidableEq I] (b : Basis I ℚ K)
    (hb : ∀ i, IsIntegral ℤ (b i)) :
    ∃ z : ℤ, z ≠ 0 ∧ Algebra.discr ℚ b = (z:ℚ)^2 * (NumberField.discr K : ℚ) := by
  classical
  let e := (NumberField.integralBasis K).indexEquiv b
  let b₀ := (NumberField.integralBasis K).reindex e
  let P := b₀.toMatrix b
  have hP : ∀ i j, IsIntegral ℤ (P i j) := by
    intro i j
    change IsIntegral ℤ ((NumberField.integralBasis K).repr (b j) (e.symm i))
    let x : 𝓞 K := ⟨b j,hb j⟩
    have hx : b j = algebraMap (𝓞 K) K x := rfl
    rw [hx,NumberField.integralBasis_repr_apply]
    exact isIntegral_algebraMap
  obtain ⟨z,hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp (IsIntegral.det hP)
  have hz0 : z ≠ 0 := by
    intro h
    have hP0 : P.det = 0 := by rw [← hz,h,_root_.map_zero]
    have hh : P.det * (b.toMatrix b₀).det = 1 := by
      rw [← Matrix.det_mul]
      simp [P]
    rw [hP0,zero_mul] at hh
    exact zero_ne_one hh
  refine ⟨z,hz0,?_⟩
  rw [← b₀.toMatrix_map_vecMul b,Algebra.discr_of_matrix_vecMul]
  change P.det ^ 2 * Algebra.discr ℚ b₀ = _
  rw [← hz]
  congr 1
  simpa only [b₀,Basis.coe_reindex,Algebra.discr_reindex] using
    (NumberField.coe_discr K).symm

 

theorem abs_discr_le_integral_basis {K I : Type*} [Field K] [NumberField K]
    [Fintype I] [DecidableEq I] (b : Basis I ℚ K)
    (hb : ∀ i, IsIntegral ℤ (b i)) :
    |(NumberField.discr K : ℝ)| ≤ |(Algebra.discr ℚ b : ℝ)| := by
  obtain ⟨z,hz,he⟩ := integralBasis_discriminant_index b hb
  have he' : (Algebra.discr ℚ b : ℝ) = (z:ℝ)^2 * (NumberField.discr K : ℝ) := by
    exact_mod_cast he
  rw [he',abs_mul,abs_pow,even_two.pow_abs]
  have hz1 : (1:ℝ) ≤ (z:ℝ)^2 := by
    have hzi : (1:ℤ) ≤ z^2 := by
      have hh : 0 < z^2 := sq_pos_of_ne_zero hz
      omega
    exact_mod_cast hzi
  nlinarith [abs_nonneg (NumberField.discr K : ℝ)]

lemma norm_det_le_factorial_pow {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) {B : ℝ} (_hB : 0 ≤ B) (hA : ∀ i j, ‖A i j‖ ≤ B) :
    ‖A.det‖ ≤ (Fintype.card I).factorial * B ^ Fintype.card I := by
  classical
  rw [Matrix.det_apply']
  calc
    ‖∑ σ : Equiv.Perm I, (Equiv.Perm.sign σ : ℂ) * ∏ i, A (σ i) i‖
        ≤ ∑ σ : Equiv.Perm I, ‖(Equiv.Perm.sign σ : ℂ) * ∏ i, A (σ i) i‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm I, B ^ Fintype.card I := by
      apply Finset.sum_le_sum
      intro σ _
      rw [norm_mul]
      have hs : ‖(Equiv.Perm.sign σ : ℂ)‖ = 1 := by
        simpa only [Complex.norm_intCast] using (abs_unit_intCast (α := ℝ) (Equiv.Perm.sign σ))
      rw [hs,one_mul,norm_prod]
      exact (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => hA (σ i) i)).trans_eq
        (by simp)
    _ = _ := by simp [Fintype.card_perm]

 

theorem abs_discr_le_integral_basis_height {K I : Type*} [Field K] [NumberField K]
    [Fintype I] [DecidableEq I] (b : Basis I ℚ K)
    (hb : ∀ i, IsIntegral ℤ (b i)) {B : ℝ} (hB : 0 ≤ B)
    (hheight : ∀ (σ : K →ₐ[ℚ] ℂ) i, ‖σ (b i)‖ ≤ B) :
    |(NumberField.discr K : ℝ)| ≤
      ((Fintype.card I).factorial * B ^ Fintype.card I)^2 := by
  classical
  let e : I ≃ (K →ₐ[ℚ] ℂ) := Fintype.equivOfCardEq (by
    rw [← finrank_eq_card_basis b,AlgHom.card])
  have he := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ ℂ b e
  have he' : |(Algebra.discr ℚ b : ℝ)| =
      ‖(Algebra.embeddingsMatrixReindex ℚ ℂ b e).det‖^2 := by
    have h := congrArg norm he
    simpa only [norm_pow,eq_ratCast,Complex.norm_ratCast] using h
  calc
    |(NumberField.discr K : ℝ)| ≤ |(Algebra.discr ℚ b : ℝ)| := abs_discr_le_integral_basis b hb
    _ = _ := he'
    _ ≤ _ := pow_le_pow_left₀ (norm_nonneg _) (norm_det_le_factorial_pow _ hB (by
      intro i j
      exact hheight (e j) i)) 2


end ArtinMatthews.KummerDiscriminant
