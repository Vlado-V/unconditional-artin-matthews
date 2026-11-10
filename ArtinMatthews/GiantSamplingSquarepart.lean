module

public import Mathlib.Data.Nat.Squarefree
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


set_option backward.privateInPublic true
@[expose] public section

/-! The unique positive square part and squarefree part of each actual
cofactor, with an exact finite reindexing of the cofactor sum. -/

noncomputable section
namespace ArtinMatthews

open scoped BigOperators

theorem giantSquarepart_unique {d a e b : ℕ}
    (hd : 0 < d) (he : 0 < e) (ha : Squarefree a) (hb : Squarefree b)
    (h : d ^ 2 * a = e ^ 2 * b) : d = e ∧ a = b := by
  have hde : d = e := by
    apply Nat.eq_of_factorization_eq hd.ne' he.ne'
    intro p
    have hpow : 2 * d.factorization p + a.factorization p =
        2 * e.factorization p + b.factorization p := by
      simpa [Nat.factorization_mul (pow_ne_zero _ hd.ne') ha.ne_zero,
        Nat.factorization_mul (pow_ne_zero _ he.ne') hb.ne_zero, Nat.factorization_pow,
        Finsupp.add_apply, Finsupp.smul_apply, nsmul_eq_mul] using
        congrArg (fun n : ℕ => n.factorization p) h
    have ha₁ := ha.natFactorization_le_one p
    have hb₁ := hb.natFactorization_le_one p
    omega
  subst e
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_left (pow_pos hd _) h⟩

def giantSquarepartCarrier (K : Finset ℕ) (B : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact (Finset.Icc 1 B ×ˢ Finset.Icc 1 B).filter fun t =>
    Squarefree t.2 ∧ t.1 ^ 2 * t.2 ∈ K

theorem giantSquarepartCarrier_sum {A : Type*} [AddCommMonoid A]
    (K : Finset ℕ) (B : ℕ) (hK : ∀ k ∈ K, 0 < k ∧ k ≤ B) (F : ℕ → A) :
    (∑ k ∈ K, F k) = ∑ t ∈ giantSquarepartCarrier K B, F (t.1 ^ 2 * t.2) := by
  classical
  symm
  apply Finset.sum_bij (fun t _ => t.1 ^ 2 * t.2)
  · intro t ht
    exact (Finset.mem_filter.mp ht).2.2
  · intro t ht s hs heq
    obtain ⟨htB, htsq, _⟩ := Finset.mem_filter.mp ht
    obtain ⟨hsB, hssq, _⟩ := Finset.mem_filter.mp hs
    have hd := (Finset.mem_Icc.mp (Finset.mem_product.mp htB).1).1
    have he := (Finset.mem_Icc.mp (Finset.mem_product.mp hsB).1).1
    obtain ⟨hds, has⟩ := giantSquarepart_unique hd he htsq hssq heq
    exact Prod.ext hds has
  · intro k hk
    obtain ⟨a, d, ha, hd, hda, hsq⟩ := Nat.sq_mul_squarefree_of_pos (hK k hk).1
    have hdvd : d ∣ k := by
      rw [← hda, pow_two, mul_assoc]
      exact dvd_mul_right _ _
    have havd : a ∣ k := by rw [← hda]; exact dvd_mul_left _ _
    have hdk := Nat.le_of_dvd (hK k hk).1 hdvd
    have hak := Nat.le_of_dvd (hK k hk).1 havd
    refine ⟨(d, a), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, hsq, ?_⟩, hda⟩
    · exact Finset.mem_Icc.mpr ⟨hd, hdk.trans (hK k hk).2⟩
    · exact Finset.mem_Icc.mpr ⟨ha, hak.trans (hK k hk).2⟩
    · simpa only [hda] using hk
  · intro _t _ht
    rfl

end ArtinMatthews
