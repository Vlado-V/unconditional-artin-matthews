module

public import ArtinMatthews.MarkedMemoryCappedRawIndex
public import ArtinMatthews.MarkedMemoryCappedPathConstruction
public import ArtinMatthews.MarkedMemoryCappedBirthFactorials
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

/-! Exact summation of the genuine ordered-birth and compatible-cap
fibers. Arbitrary signed choice coefficients and copied-order tests are
retained. No factorial or coverage identity is a premise. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2) (z₀ : Z) (q : ℝ)

theorem markedMemoryCappedRawDecorated_sum
    (T : MarkedMemoryActivePathData P pads Z n → (Fin n → J → Equiv.Perm (Fin pads)) → ℂ) :
    (∑ x : MarkedMemoryCappedRawDecoratedIndex (P := P) (pads := pads) (B := B) (n := n) hZ z₀,
      ((markedMemoryPathPrimeChoiceWeight hZ x.1.1 q x.2.1.choices /
        markedMemoryIndependentBirthFactorials hZ
          (markedMemoryCappedPathIndependent (B := B) hZ x.1.1 x.2.1.choices
            x.2.1.compatible x.2.1.capacity x.2.2.1):ℝ):ℂ)*T x.1.1 x.2.2.2)=
      ∑ d : {d : MarkedMemoryActivePathData P pads Z n // d.position 0=z₀},
        (markedMemoryPathCappedChoiceSum hZ d.1 q B:ℂ)*
          ∑ order : Fin n → J → Equiv.Perm (Fin pads),T d.1 order := by
  simp only [Fintype.sum_sigma,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro d _
  have hb (c : MarkedMemoryCappedChoiceIndex (B := B) hZ d.1) :
      (∑ births : MarkedMemoryEndpointBirthOrders (markedMemoryPathEndpointData hZ d.1 c.choices c.compatible),
        ∑ order : Fin n → J → Equiv.Perm (Fin pads),
          ((markedMemoryPathPrimeChoiceWeight hZ d.1 q c.choices /
            markedMemoryIndependentBirthFactorials hZ
              (markedMemoryCappedPathIndependent (B := B) hZ d.1 c.choices c.compatible c.capacity births):ℝ):ℂ)*
            T d.1 order)=
        (markedMemoryPathPrimeChoiceWeight hZ d.1 q c.choices:ℂ)*∑ order,T d.1 order := by
    rw [Finset.sum_comm,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro order _
    rw [← Finset.sum_mul,markedMemoryCappedPath_birthFactorials_sum]
  calc
    _ = (∑ c : MarkedMemoryCappedChoiceIndex (B := B) hZ d.1,
        (markedMemoryPathPrimeChoiceWeight hZ d.1 q c.choices:ℂ))*∑ order,T d.1 order := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun c _ => hb c)
    _ = _ := by
      rw [← Complex.ofReal_sum,markedMemoryCappedChoiceIndex_weight_sum]

end
end ArtinMatthews
