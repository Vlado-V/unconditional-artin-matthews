module

public import ArtinMatthews.SourceKPAdeleCoordinates
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

/-! A matrix supported at one actual finite place. Every other
component is the identity, and the construction respects matrix
multiplication and inverses. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open scoped NumberField MatrixGroups AdeleRing Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K]
    (P : HeightOneSpectrum (𝓞 K))

def sourceKPAdeleSingleEntries (a : Matrix (Fin 2) (Fin 2) (P.adicCompletion K)) :
    Matrix (Fin 2) (Fin 2) 𝔸ᶠ[K] :=
  Matrix.of fun i j =>
    (1 : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[K]) i j +
      (show 𝔸ᶠ[K] from RestrictedProduct.single
        (fun Q : HeightOneSpectrum (𝓞 K) => Q.adicCompletionIntegers K) P
          (a i j - (1 : Matrix (Fin 2) (Fin 2) (P.adicCompletion K)) i j))

theorem sourceKPAdeleSingleEntries_same (a : Matrix (Fin 2) (Fin 2) (P.adicCompletion K)) (i j : Fin 2) :
    sourceKPAdeleSingleEntries K P a i j P = a i j := by
  change (1 : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[K]) i j P +
    RestrictedProduct.single (fun Q : HeightOneSpectrum (𝓞 K) => Q.adicCompletionIntegers K) P
      (a i j - (1 : Matrix (Fin 2) (Fin 2) (P.adicCompletion K)) i j) P = a i j
  rw [RestrictedProduct.single_eq_same]
  have he : (1 : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[K]) i j P =
      (1 : Matrix (Fin 2) (Fin 2) (P.adicCompletion K)) i j := by
    by_cases h : i = j <;> simp [Matrix.one_apply, h] <;> rfl
  rw [he, add_sub_cancel]

theorem sourceKPAdeleSingleEntries_other (a : Matrix (Fin 2) (Fin 2) (P.adicCompletion K))
    (Q : HeightOneSpectrum (𝓞 K)) (hQP : Q ≠ P) (i j : Fin 2) :
    sourceKPAdeleSingleEntries K P a i j Q =
      (1 : Matrix (Fin 2) (Fin 2) (Q.adicCompletion K)) i j := by
  change (1 : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[K]) i j Q +
    RestrictedProduct.single (fun Q : HeightOneSpectrum (𝓞 K) => Q.adicCompletionIntegers K) P
      (a i j - (1 : Matrix (Fin 2) (Fin 2) (P.adicCompletion K)) i j) Q = _
  rw [RestrictedProduct.single_eq_of_ne _ _ hQP, add_zero]
  by_cases h : i = j <;> simp [Matrix.one_apply, h] <;> rfl

theorem sourceKPAdeleSingleEntries_mul (a b : Matrix (Fin 2) (Fin 2) (P.adicCompletion K)) :
    sourceKPAdeleSingleEntries K P (a * b) =
      sourceKPAdeleSingleEntries K P a * sourceKPAdeleSingleEntries K P b := by
  apply Matrix.ext
  intro i j
  apply Subtype.ext
  funext Q
  change sourceKPAdeleSingleEntries K P (a * b) i j Q =
    ∑ k : Fin 2, sourceKPAdeleSingleEntries K P a i k Q * sourceKPAdeleSingleEntries K P b k j Q
  by_cases h : Q = P
  · subst Q
    simp only [sourceKPAdeleSingleEntries_same, Matrix.mul_apply]
  · simp only [sourceKPAdeleSingleEntries_other K P _ Q h]
    simpa only [Matrix.mul_apply] using congrArg (fun M : Matrix (Fin 2) (Fin 2) (Q.adicCompletion K) => M i j) (one_mul 1).symm

theorem sourceKPAdeleSingleEntries_one :
    sourceKPAdeleSingleEntries K P (1 : Matrix (Fin 2) (Fin 2) (P.adicCompletion K)) = 1 := by
  apply Matrix.ext
  intro i j
  apply Subtype.ext
  funext Q
  change sourceKPAdeleSingleEntries K P 1 i j Q = (1 : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[K]) i j Q
  by_cases h : Q = P
  · subst Q
    rw [sourceKPAdeleSingleEntries_same]
    by_cases he : i = j <;> simp [Matrix.one_apply, he] <;> rfl
  · rw [sourceKPAdeleSingleEntries_other K P _ Q h]
    by_cases he : i = j <;> simp [Matrix.one_apply, he] <;> rfl

def sourceKPAdeleSingleMatrix : GL (Fin 2) (P.adicCompletion K) →* GL (Fin 2) 𝔸ᶠ[K] where
  toFun g :=
    { val := sourceKPAdeleSingleEntries K P g.val
      inv := sourceKPAdeleSingleEntries K P g.inv
      val_inv := by rw [← sourceKPAdeleSingleEntries_mul, g.val_inv, sourceKPAdeleSingleEntries_one]
      inv_val := by rw [← sourceKPAdeleSingleEntries_mul, g.inv_val, sourceKPAdeleSingleEntries_one] }
  map_one' := Units.ext (sourceKPAdeleSingleEntries_one K P)
  map_mul' g h := Units.ext (sourceKPAdeleSingleEntries_mul K P g.val h.val)

theorem sourceKPAdeleSingleMatrix_same (g : GL (Fin 2) (P.adicCompletion K)) :
    sourceKPAdeleMatrixAt K P (sourceKPAdeleSingleMatrix K P g) = g := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  exact sourceKPAdeleSingleEntries_same K P g.val i j

theorem sourceKPAdeleSingleMatrix_other (Q : HeightOneSpectrum (𝓞 K)) (hQP : Q ≠ P)
    (g : GL (Fin 2) (P.adicCompletion K)) :
    sourceKPAdeleMatrixAt K Q (sourceKPAdeleSingleMatrix K P g) = 1 := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  exact sourceKPAdeleSingleEntries_other K P g.val Q hQP i j

theorem sourceKPAdeleMatrixAt_ext {g h : GL (Fin 2) 𝔸ᶠ[K]}
    (he : ∀ Q, sourceKPAdeleMatrixAt K Q g = sourceKPAdeleMatrixAt K Q h) : g = h := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  apply Subtype.ext
  funext Q
  exact congrArg (fun m : GL (Fin 2) (Q.adicCompletion K) => m i j) (he Q)

theorem sourceKPAdeleSingleMatrix_commute (Q : HeightOneSpectrum (𝓞 K)) (hQP : Q ≠ P)
    (g : GL (Fin 2) (P.adicCompletion K)) (h : GL (Fin 2) (Q.adicCompletion K)) :
    Commute (sourceKPAdeleSingleMatrix K P g) (sourceKPAdeleSingleMatrix K Q h) := by
  apply sourceKPAdeleMatrixAt_ext K
  intro R
  simp only [map_mul]
  by_cases hRP : R = P
  · subst R
    rw [sourceKPAdeleSingleMatrix_same, sourceKPAdeleSingleMatrix_other K Q P hQP.symm, mul_one, one_mul]
  · by_cases hRQ : R = Q
    · subst R
      rw [sourceKPAdeleSingleMatrix_other K P Q hQP, sourceKPAdeleSingleMatrix_same, one_mul, mul_one]
    · rw [sourceKPAdeleSingleMatrix_other K P R hRP, sourceKPAdeleSingleMatrix_other K Q R hRQ]

end
end ArtinMatthews
