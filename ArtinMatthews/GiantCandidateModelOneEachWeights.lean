module

public import ArtinMatthews.GiantCandidateModelOneEachEvent
public import ArtinMatthews.GiantCandidateModelNoHitProduct
public import ArtinMatthews.GiantCandidatePrimeHitLower
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
public import Mathlib.Tactic.Basify
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! The ordered distinct pairs of hit atoms carry a fixed positive
reciprocal mass once the single-prime atoms are sufficiently small. -/

namespace ArtinMatthews
noncomputable section
open Finset
open scoped BigOperators

theorem giantCandidateModelOneEach_weights_ge {ι : Type*} [Fintype ι] (G : ι → Finset ℕ)
    (hG : ∀ i p,p∈G i → p.Prime) {j : ℕ} (hj : 0<j)
    (hlarge : ∀ p : giantCandidateSelectionPrimes G,2*(j:ℝ)≤(p.val:ℝ))
    (hsmall : ∀ p : giantCandidateSelectionPrimes G,(j:ℝ)/(p.val:ℝ)≤
      (∑ a : giantCandidateSelectionPrimes G,1/(a.val:ℝ))/2) :
    let V := ∑ p : giantCandidateSelectionPrimes G,1/(p.val:ℝ)
    V^2/4≤∑ ab∈giantCandidateModelOneEachPairs G,
      giantCandidateModelHitAtom G hG j ab.1 .predecessor*
        giantCandidateModelHitAtom G hG j ab.2 .product := by
  let U := giantCandidateSelectionPrimes G
  let V := ∑ p : U,1/(p.val:ℝ)
  let A (p : U) := giantCandidateModelHitAtom G hG j p .predecessor
  let B (p : U) := giantCandidateModelHitAtom G hG j p .product
  let P := giantCandidateModelOneEachPairs G
  have hV : 0≤V := sum_nonneg (fun _ _ => by positivity)
  have hA (p : U) : 1/(2*(p.val:ℝ))≤A p := by
    let _ : Fact p.val.Prime := ⟨giantCandidateModelPrime_prime G hG p⟩
    dsimp only [A]
    rw [giantCandidateModelHitAtom_eq]
    exact giantCandidatePrimeHitProbability_predecessor_lower p.val j hj (hlarge p)
  have hB (p : U) : 1/(p.val:ℝ)≤B p := by
    let _ : Fact p.val.Prime := ⟨giantCandidateModelPrime_prime G hG p⟩
    dsimp only [B]
    rw [giantCandidateModelHitAtom_eq]
    exact giantCandidatePrimeHitProbability_product_lower p.val j hj
  have hAsum : V/2≤∑ p : U,A p := by
    calc
      _ = ∑ p : U,1/(2*(p.val:ℝ)) := by
        unfold V
        rw [sum_div]
        exact sum_congr rfl (fun _ _ => by ring)
      _ ≤ _ := sum_le_sum (fun p _ => hA p)
  have hBsum : V≤∑ p : U,B p := sum_le_sum (fun p _ => hB p)
  have hBerase (p : U) : V/2≤∑ a∈univ.erase p,B a := by
    have hp := (giantCandidateModelHitAtom_le G hG hj p .product).trans (hsmall p)
    have he := sum_erase_add (univ : Finset U) B (mem_univ p)
    change B p≤V/2 at hp
    linarith only [hBsum,hp,he]
  have heq : (∑ ab∈P,A ab.1*B ab.2)=∑ a : U,A a*(∑ b∈univ.erase a,B b) := by
    unfold P giantCandidateModelOneEachPairs
    rw [sum_filter,sum_product]
    apply sum_congr rfl
    intro a _
    rw [← sum_filter,mul_sum]
    have he : ((univ : Finset U).filter (fun b => a≠b))=univ.erase a := by
      ext b
      simp only [mem_filter,mem_univ,true_and,mem_erase,and_true]
      exact ne_comm
    rw [he]
  change V^2/4≤∑ ab∈P,A ab.1*B ab.2
  rw [heq]
  calc
    _ = (V/2)*(V/2) := by ring
    _ ≤ (∑ a : U,A a)*(V/2) := mul_le_mul_of_nonneg_right hAsum (by positivity)
    _ = ∑ a : U,A a*(V/2) := sum_mul _ _ _
    _ ≤ _ := sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (hBerase a)
      (giantCandidateModelHitAtom_nonneg G hG j a .predecessor))

end
end ArtinMatthews
