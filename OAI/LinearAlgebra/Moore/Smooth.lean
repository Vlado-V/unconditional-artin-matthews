module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.LinearAlgebra.Moore.Cofactor
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import OAI.LinearAlgebra.Moore.Inverse


set_option backward.privateInPublic true
@[expose] public section

/-! Smoothness of the signed determinant, its differential, and its cofactor,
including at singular matrices. -/

noncomputable section

namespace OAI.LinearAlgebra.Moore

open Matrix
open scoped ContDiff Matrix.Norms.Elementwise

theorem contDiff_skewComplexify_entry {n : ℕ} (k : ℕ∞ω) (i j : Fin n × Fin 2) :
    ContDiff ℝ k (fun A : Matrix (Fin n) (Fin n) (Quaternion ℝ) ↦ skewComplexify A i j) := by
  exact (skewQuaternionEntryCLM i.2 j.2).contDiff.comp
    (contDiff_apply_apply ℝ (Quaternion ℝ) i.1 j.1)

theorem contDiff_mooreDet (n : ℕ) (k : ℕ∞ω) : ContDiff ℝ k (mooreDet n) := by
  change ContDiff ℝ k (Complex.reCLM ∘ fun A : Matrix (Fin n) (Fin n) (Quaternion ℝ) ↦
    pfaffian n (skewComplexify A))
  apply (Complex.reCLM.contDiff : ContDiff ℝ k Complex.reCLM).comp
  unfold pfaffian
  apply contDiff_const.mul
  apply ContDiff.sum
  intro σ _
  apply contDiff_const.mul
  apply contDiff_prod
  intro i _
  exact contDiff_skewComplexify_entry k (σ (i, 0)) (σ (i, 1))

theorem contDiff_mooreDifferential_left (n : ℕ) (k : ℕ∞ω)
    (D : Matrix (Fin n) (Fin n) (Quaternion ℝ)) :
    ContDiff ℝ k (fun A ↦ mooreDifferential n A D) := by
  change ContDiff ℝ k (Complex.reCLM ∘ fun A : Matrix (Fin n) (Fin n) (Quaternion ℝ) ↦
    pfaffianDifferential n (skewComplexify A) (skewComplexify D))
  apply (Complex.reCLM.contDiff : ContDiff ℝ k Complex.reCLM).comp
  unfold pfaffianDifferential
  apply contDiff_const.mul
  apply ContDiff.sum
  intro σ _
  apply contDiff_const.mul
  apply ContDiff.sum
  intro i _
  apply ContDiff.mul _ contDiff_const
  apply contDiff_prod
  intro j _
  exact contDiff_skewComplexify_entry k (σ (j, 0)) (σ (j, 1))

theorem quaternionDualVector_eq (L : Quaternion ℝ →ₗ[ℝ] ℝ) :
    quaternionDualVector L = L 1 • (1 : Quaternion ℝ) +
      L ⟨0, 1, 0, 0⟩ • (⟨0, 1, 0, 0⟩ : Quaternion ℝ) +
      L ⟨0, 0, 1, 0⟩ • (⟨0, 0, 1, 0⟩ : Quaternion ℝ) +
      L ⟨0, 0, 0, 1⟩ • (⟨0, 0, 0, 1⟩ : Quaternion ℝ) := by
  ext <;> simp [quaternionDualVector]

theorem contDiff_rawCofactor (n : ℕ) (k : ℕ∞ω) : ContDiff ℝ k (rawCofactor n) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  simp only [rawCofactor, quaternionDualVector_eq]
  apply quaternionStarCLM.contDiff.comp
  change ContDiff ℝ k (fun A ↦
    mooreDifferential n A (single j i 1) • (1 : Quaternion ℝ) +
      mooreDifferential n A (single j i ⟨0, 1, 0, 0⟩) • (⟨0, 1, 0, 0⟩ : Quaternion ℝ) +
      mooreDifferential n A (single j i ⟨0, 0, 1, 0⟩) • (⟨0, 0, 1, 0⟩ : Quaternion ℝ) +
      mooreDifferential n A (single j i ⟨0, 0, 0, 1⟩) • (⟨0, 0, 0, 1⟩ : Quaternion ℝ))
  exact (((contDiff_mooreDifferential_left n k _).smul contDiff_const).add
    ((contDiff_mooreDifferential_left n k _).smul contDiff_const) |>.add
    ((contDiff_mooreDifferential_left n k _).smul contDiff_const)).add
    ((contDiff_mooreDifferential_left n k _).smul contDiff_const)

theorem contDiff_mooreCofactor (n : ℕ) (k : ℕ∞ω) : ContDiff ℝ k (mooreCofactor n) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  change ContDiff ℝ k (fun A ↦ (1 / 2 : ℝ) •
    (rawCofactor n A i j + star (rawCofactor n A j i)))
  have h₁ := (contDiff_pi.mp (contDiff_pi.mp (contDiff_rawCofactor n k) i)) j
  have h₂ := quaternionStarCLM.contDiff.comp
    ((contDiff_pi.mp (contDiff_pi.mp (contDiff_rawCofactor n k) j)) i)
  exact (contDiff_const : ContDiff ℝ k (fun _ : Matrix (Fin n) (Fin n) (Quaternion ℝ) ↦
    (1 / 2 : ℝ))).smul (h₁.add h₂)

end OAI.LinearAlgebra.Moore
