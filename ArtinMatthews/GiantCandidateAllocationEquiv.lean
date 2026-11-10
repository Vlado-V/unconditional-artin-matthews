module

public import ArtinMatthews.GiantCandidatePrimeStrip
public import ArtinMatthews.GiantCandidateAllocationParts
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

/-! Splitting every actual ordered factorization into its active and
stripped factors gives a genuine finite equivalence. The squarefree
active fiber then counts the choices for the active prime allocations. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section

theorem giantCandidateStrip_idem (P : Finset ℕ) (n : ℕ) :
    giantCandidateStrip P (giantCandidateStrip P n) = giantCandidateStrip P n := by
  by_cases hn : n = 0
  · subst n
    simp [giantCandidateStrip]
  · have h := giantCandidatePrimePart_eq_one_of_coprime P
      (giantCandidateStrip_pos P (Nat.pos_of_ne_zero hn)) (giantCandidateStrip_coprime P hn)
    change giantCandidateStrip P n / giantCandidatePrimePart P (giantCandidateStrip P n) = _
    rw [h, Nat.div_one]

/-- The first factor remembers the stripped tuple. The second remembers
the active part allocated to each slot, including any multiplicities. -/
def giantCandidateAllocationEquiv (P : Finset ℕ) (j n : ℕ) (hn : 0 < n) :
    ↥(giantOrderedProductFiber j n) ≃
      ↥(giantOrderedProductFiber j (giantCandidateStrip P n)) ×
      ↥(giantOrderedProductFiber j (giantCandidatePrimePart P n)) where
  toFun t := by
    obtain ⟨ht, hprod⟩ := mem_giantOrderedProductFiber.mp t.property
    exact ⟨⟨fun i => giantCandidateStrip P (t.val i), mem_giantOrderedProductFiber.mpr
        ⟨fun i => giantCandidateStrip_pos P (ht i), by
          rw [← giantCandidateStrip_prod P univ t.val (fun i _ => ht i), hprod]⟩⟩,
      ⟨fun i => giantCandidatePrimePart P (t.val i), mem_giantOrderedProductFiber.mpr
        ⟨fun i => Nat.pos_of_ne_zero (commonPrimePart_ne_zero (ht i).ne' _), by
          rw [← giantCandidatePrimePart_prod P univ t.val (fun i _ => ht i), hprod]⟩⟩⟩
  invFun s := by
    obtain ⟨he, hprodE⟩ := mem_giantOrderedProductFiber.mp s.1.property
    obtain ⟨ha, hprodA⟩ := mem_giantOrderedProductFiber.mp s.2.property
    refine ⟨fun i => s.1.val i * s.2.val i, mem_giantOrderedProductFiber.mpr
      ⟨fun i => Nat.mul_pos (he i) (ha i), ?_⟩⟩
    rw [prod_mul_distrib, hprodE, hprodA, mul_comm, giantCandidatePrimePart_mul_strip]
  left_inv t := by
    apply Subtype.ext
    funext i
    change giantCandidateStrip P (t.val i) * giantCandidatePrimePart P (t.val i) = t.val i
    rw [mul_comm, giantCandidatePrimePart_mul_strip]
  right_inv s := by
    obtain ⟨he, _⟩ := mem_giantOrderedProductFiber.mp s.1.property
    obtain ⟨ha, _⟩ := mem_giantOrderedProductFiber.mp s.2.property
    have hpart (i : Fin j) :
        giantCandidatePrimePart P (s.1.val i * s.2.val i) = s.2.val i := by
      have hc := Nat.Coprime.of_dvd_right (Nat.dvd_of_mem_finMulAntidiag s.1.property i)
        (giantCandidateStrip_coprime P hn.ne')
      have he' := giantCandidatePrimePart_eq_one_of_coprime P (he i) hc
      have ha' := giantCandidatePrimePart_eq_self_of_dvd_part P hn
        (Nat.dvd_of_mem_finMulAntidiag s.2.property i)
      calc
        _ = giantCandidatePrimePart P (s.1.val i) * giantCandidatePrimePart P (s.2.val i) :=
          commonPrimePart_mul (he i).ne' (ha i).ne' _
        _ = _ := by rw [he', ha', one_mul]
    apply Prod.ext
    · apply Subtype.ext
      funext i
      change giantCandidateStrip P (s.1.val i * s.2.val i) = s.1.val i
      apply Nat.eq_of_mul_eq_mul_left (ha i)
      calc
        _ = giantCandidatePrimePart P (s.1.val i * s.2.val i) *
            giantCandidateStrip P (s.1.val i * s.2.val i) := by rw [hpart]
        _ = s.1.val i * s.2.val i := giantCandidatePrimePart_mul_strip P _
        _ = _ := mul_comm _ _
    · apply Subtype.ext
      funext i
      exact hpart i

theorem giantCandidateAllocationEquiv_symm_apply (P : Finset ℕ) (j n : ℕ)
    (hn : 0 < n) (s : ↥(giantOrderedProductFiber j (giantCandidateStrip P n)) ×
      ↥(giantOrderedProductFiber j (giantCandidatePrimePart P n))) (i : Fin j) :
    ((giantCandidateAllocationEquiv P j n hn).symm s).val i = s.1.val i * s.2.val i := rfl

theorem giantCandidatePrimePart_fiber_card (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (j : ℕ) {n : ℕ} (hn : 0 < n) (hnsq : ∀ p ∈ P, ¬ p ^ 2 ∣ n) :
    (giantOrderedProductFiber j (giantCandidatePrimePart P n)).card = j ^ bandCount P n := by
  rw [Nat.card_finMulAntidiag_of_squarefree (giantCandidatePrimePart_squarefree P hP hn hnsq)]
  simp only [ArithmeticFunction.cardDistinctFactors_apply, ← List.card_toFinset,
    Nat.toFinset_factors, giantCandidatePrimePart_primeFactors P hP hn, bandCount]

end
end ArtinMatthews
