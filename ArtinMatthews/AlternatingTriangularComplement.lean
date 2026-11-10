module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
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
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

/-! The coordinate complement step for the exponent-two/three Hilbert spaces.
The triangular construction works in characteristic two as well: no division
by two is used. Arithmetic identification of the Hilbert spaces is separate. -/

namespace ArtinMatthews

noncomputable section

open Matrix

variable {K : Type*} [Field K] {n : ℕ}

def alternatingUpper (A : Matrix (Fin n) (Fin n) K) : Matrix (Fin n) (Fin n) K :=
  fun i j => if i < j then A i j else 0

theorem alternatingUpper_sub_transpose (A : Matrix (Fin n) (Fin n) K)
    (hdiag : ∀ i, A i i = 0) (hskew : ∀ i j, A j i = -A i j) :
    alternatingUpper A - (alternatingUpper A)ᵀ = A := by
  ext i j
  rcases lt_trichotomy i j with h | rfl | h
  · simp [alternatingUpper, h, not_lt_of_gt h]
  · simp [alternatingUpper, hdiag]
  · simp [alternatingUpper, h, not_lt_of_gt h, hskew i j]

def splitAlternatingForm (A : Matrix (Fin n) (Fin n) K)
    (x y : (Fin n → K) × (Fin n → K)) : K :=
  x.1 ⬝ᵥ y.2 - x.2 ⬝ᵥ y.1 + x.2 ⬝ᵥ A *ᵥ y.2

def alternatingGraphMap (T : Matrix (Fin n) (Fin n) K) :
    (Fin n → K) →ₗ[K] ((Fin n → K) × (Fin n → K)) :=
  (Matrix.toLin' T).prod LinearMap.id

theorem alternatingGraph_isotropic (A : Matrix (Fin n) (Fin n) K)
    (hdiag : ∀ i, A i i = 0) (hskew : ∀ i j, A j i = -A i j)
    (x y : Fin n → K) :
    splitAlternatingForm A (alternatingGraphMap (alternatingUpper A) x)
      (alternatingGraphMap (alternatingUpper A) y) = 0 := by
  change ((alternatingUpper A) *ᵥ x) ⬝ᵥ y - x ⬝ᵥ (alternatingUpper A) *ᵥ y +
    x ⬝ᵥ A *ᵥ y = 0
  have h := alternatingUpper_sub_transpose A hdiag hskew
  have hm : x ⬝ᵥ A *ᵥ y = x ⬝ᵥ (alternatingUpper A) *ᵥ y -
      x ⬝ᵥ (alternatingUpper A)ᵀ *ᵥ y := by
    simpa only [Matrix.sub_mulVec, dotProduct_sub] using
      (congrArg (fun M : Matrix (Fin n) (Fin n) K => x ⬝ᵥ M *ᵥ y) h).symm
  have ht : ((alternatingUpper A) *ᵥ x) ⬝ᵥ y =
      x ⬝ᵥ (alternatingUpper A)ᵀ *ᵥ y := by
    rw [Matrix.dotProduct_transpose_mulVec, dotProduct_comm]
  rw [ht, hm]
  ring

theorem alternatingGraph_isCompl (T : Matrix (Fin n) (Fin n) K) :
    IsCompl (LinearMap.ker (LinearMap.snd K (Fin n → K) (Fin n → K)))
      (LinearMap.range (alternatingGraphMap T)) := by
  rw [isCompl_iff]
  constructor
  · rw [Submodule.disjoint_def]
    intro z hz hzg
    obtain ⟨y, rfl⟩ := hzg
    have hy : y = 0 := by simpa [alternatingGraphMap] using hz
    simp [hy]
  · rw [codisjoint_iff]
    apply top_unique
    intro z _
    rw [Submodule.mem_sup]
    refine ⟨(z.1 - T *ᵥ z.2, 0), ?_, (T *ᵥ z.2, z.2), ?_, ?_⟩
    · simp
    · exact ⟨z.2, rfl⟩
    · ext <;> simp

theorem exists_splitAlternating_isotropic_complement
    (A : Matrix (Fin n) (Fin n) K)
    (hdiag : ∀ i, A i i = 0) (hskew : ∀ i j, A j i = -A i j) :
    ∃ T : Matrix (Fin n) (Fin n) K,
      IsCompl (LinearMap.ker (LinearMap.snd K (Fin n → K) (Fin n → K)))
        (LinearMap.range (alternatingGraphMap T)) ∧
      ∀ x y, splitAlternatingForm A (alternatingGraphMap T x)
        (alternatingGraphMap T y) = 0 :=
  ⟨alternatingUpper A, alternatingGraph_isCompl _, alternatingGraph_isotropic A hdiag hskew⟩

end

end ArtinMatthews
