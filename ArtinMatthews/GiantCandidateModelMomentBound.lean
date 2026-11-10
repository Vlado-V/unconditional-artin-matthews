module

public import ArtinMatthews.GiantCandidateBoxBinomialMoment
public import ArtinMatthews.GiantCandidateSelectionModelBound
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
public import OAI.NumberTheory.Jacobsthal.Analysis.BonferroniDensity


set_option backward.privateInPublic true
@[expose] public section

/-! The independent model's fixed joint moments have the factorial
bound from the genuine reciprocal masses of the groups. -/

namespace ArtinMatthews
noncomputable section
open Finset
open OAI.Erdos970.NumberTheoryLean.BonferroniDensity
open scoped BigOperators

theorem giantCandidateModelBinomialMoment_nonneg {ι : Type*} [Fintype ι] (j : ℕ)
    (G : ι → Finset ℕ) (side : ι → GiantCandidateHitSide) (k : ι → ℕ)
    (hG : ∀ i p,p∈G i → p.Prime) :
    0≤giantCandidateModelBinomialMoment j G side k hG := by
  unfold giantCandidateModelBinomialMoment
  exact sum_nonneg (fun _ _ => prod_nonneg (fun _ _ => by positivity))

theorem giantCandidateModelBinomialMoment_le {ι : Type*} [Fintype ι] {j : ℕ} (hj : 0<j)
    (G : ι → Finset ℕ) (side : ι → GiantCandidateHitSide) (k : ι → ℕ)
    (hG : ∀ i p,p∈G i → p.Prime)
    (hdis : Pairwise (fun i l => side i=side l → Disjoint (G i) (G l)))
    {B : ℝ} (hB : 0≤B) (hmass : ∀ i,(∑ p∈G i,1/(p:ℝ))≤B) :
    giantCandidateModelBinomialMoment j G side k hG ≤
      ∏ i,((j:ℝ)*B)^(k i)/((k i).factorial:ℝ) := by
  classical
  let w (p : ℕ) : ℝ := (j:ℝ)/(p:ℝ)
  have hw (p : ℕ) : 0≤w p := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hsum (i : ι) : (∑ p∈G i,w p)≤(j:ℝ)*B := by
    calc
      _ = (j:ℝ)*(∑ p∈G i,1/(p:ℝ)) := by
        rw [mul_sum]
        exact sum_congr rfl (fun _ _ => (mul_one_div _ _).symm)
      _ ≤ _ := mul_le_mul_of_nonneg_left (hmass i) (Nat.cast_nonneg _)
  unfold giantCandidateModelBinomialMoment
  calc
    _ ≤ ∑ D : giantCandidateHitSelections G k,∏ i,∏ p∈D.val i,w p :=
      sum_le_sum (fun D _ => giantCandidateSelectionModelMass_le_product D.property side hdis
        (giantCandidateSelectionPrimes_prime D.property hG) hj)
    _ = ∑ D∈giantCandidateHitSelections G k,∏ i,∏ p∈D i,w p :=
      sum_coe_sort (giantCandidateHitSelections G k) (fun D => ∏ i,∏ p∈D i,w p)
    _ = ∏ i,∑ A∈(G i).powersetCard (k i),∏ p∈A,w p :=
      (prod_univ_sum (fun i => (G i).powersetCard (k i)) (fun _ A => ∏ p∈A,w p)).symm
    _ ≤ _ := by
      apply prod_le_prod₀
      · exact fun i _ => sum_nonneg (fun A _ => prod_nonneg (fun p _ => hw p))
      · intro i _
        exact elementarySum_le_pow_div_factorial (G i) w (fun p _ => hw p)
          (mul_nonneg (Nat.cast_nonneg _) hB) (hsum i) (k i)

end
end ArtinMatthews
