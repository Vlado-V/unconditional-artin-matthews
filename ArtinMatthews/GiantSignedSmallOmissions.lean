module

public import ArtinMatthews.MarkedPhysicalMarking
public import ArtinMatthews.MarkedMinorArcRawMemoryBulkFactorial
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
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Monotonicity.Lemmas
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
public import Mathlib.Topology.Sheaves.Presheaf


set_option backward.privateInPublic true
@[expose] public section

/-! Actual independent small-group omissions. The labels keep their
original indices, and the integer products determine the omitted subsets. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

abbrev GiantSignedSmallOmission (S : Type*) (M ell : ℕ) :=
  (g : S) → MarkedRawDeletionBatch M ell

def giantSignedSmallOmittedProduct {S : Type*} [Fintype S] {P : S → Finset ℕ} {M ell : ℕ}
    (a : MarkedPhysicalMarking P M) (U : GiantSignedSmallOmission S M ell) : ℕ :=
  ∏ g, ∏ i ∈ (U g).1, (a g i : ℕ)

def giantSignedSmallCopiedProduct {S : Type*} [Fintype S] {P : S → Finset ℕ} {M ell : ℕ}
    (a : MarkedPhysicalMarking P M) (U : GiantSignedSmallOmission S M ell) : ℕ :=
  ∏ g, ∏ i ∈ (U g).1ᶜ, (a g i : ℕ)

def giantSignedSmallOmissionNumber (S : Type*) [Fintype S] (M ell : ℕ) : ℕ :=
  (M.choose ell) ^ Fintype.card S

theorem giantSignedSmallOmission_card (S : Type*) [Fintype S] [DecidableEq S] (M ell : ℕ) :
    Fintype.card (GiantSignedSmallOmission S M ell) = giantSignedSmallOmissionNumber S M ell := by
  simp only [GiantSignedSmallOmission, Fintype.card_pi, markedRawDeletionBatch_card,
    Finset.prod_const, Finset.card_univ, giantSignedSmallOmissionNumber]

theorem giantSignedSmallOmissionNumber_pos (S : Type*) [Fintype S] (kCopy ell : ℕ) :
    0 < giantSignedSmallOmissionNumber S (kCopy + ell) ell :=
  pow_pos (Nat.choose_pos (by omega)) _

theorem giantSignedSmallCopied_mul_omitted {S : Type*} [Fintype S]
    {P : S → Finset ℕ} {M ell : ℕ} (a : MarkedPhysicalMarking P M)
    (U : GiantSignedSmallOmission S M ell) :
    giantSignedSmallCopiedProduct a U * giantSignedSmallOmittedProduct a U =
      markedPhysicalMarkingProduct a := by
  unfold giantSignedSmallCopiedProduct giantSignedSmallOmittedProduct markedPhysicalMarkingProduct
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro g _
  rw [mul_comm]
  exact Finset.prod_mul_prod_compl (U g).1 (fun i => (a g i : ℕ))

theorem giantSignedSmallOmittedProduct_pos {S : Type*} [Fintype S]
    {P : S → Finset ℕ} {M ell : ℕ} (hP : ∀ g p, p ∈ P g → p.Prime)
    (a : MarkedPhysicalMarking P M) (U : GiantSignedSmallOmission S M ell) :
    0 < giantSignedSmallOmittedProduct a U := by
  unfold giantSignedSmallOmittedProduct
  apply Finset.prod_pos
  intro g _
  exact Finset.prod_pos fun i _ => (hP g _ (a g i).property).pos

theorem giantSignedSmallOmittedProduct_injective {S : Type*} [Fintype S]
    {P : S → Finset ℕ} {M ell : ℕ} (hP : ∀ g p, p ∈ P g → p.Prime)
    (hdis : Pairwise (fun g h => Disjoint (P g) (P h)))
    (a : MarkedPhysicalMarking P M) (ha : MarkedPhysicalMarkingDistinct a) :
    Function.Injective (giantSignedSmallOmittedProduct (ell := ell) a) := by
  classical
  intro U V hUV
  funext g
  apply Subtype.ext
  apply Finset.eq_of_subset_of_card_le
  · intro i hi
    have hp : (a g i : ℕ).Prime := hP g _ (a g i).property
    have hd : (a g i : ℕ) ∣ giantSignedSmallOmittedProduct a V := by
      rw [← hUV]
      exact dvd_trans (Finset.dvd_prod_of_mem (fun k => (a g k : ℕ)) hi)
        (Finset.dvd_prod_of_mem (fun h => ∏ k ∈ (U h).1, (a h k : ℕ)) (Finset.mem_univ g))
    unfold giantSignedSmallOmittedProduct at hd
    obtain ⟨h, _, hh⟩ := (hp.prime.dvd_finsetProd_iff _).mp hd
    obtain ⟨j, hj, hij⟩ := (hp.prime.dvd_finsetProd_iff _).mp hh
    have he : (a g i : ℕ) = (a h j : ℕ) :=
      (Nat.prime_dvd_prime_iff_eq hp (hP h _ (a h j).property)).mp hij
    have hgh : g = h := by
      by_contra hn
      exact Finset.disjoint_left.mp (hdis hn) (a g i).property (he.symm ▸ (a h j).property)
    subst h
    have hindex : i = j := ha g (Subtype.ext he)
    exact hindex ▸ hj
  · simp only [markedRawDeletionBatch_deleted_card, le_refl]

def giantSignedSmallOmissionWeight (S : Type*) [Fintype S] (M ell : ℕ)
    (_U : GiantSignedSmallOmission S M ell) : ℝ :=
  (giantSignedSmallOmissionNumber S M ell : ℝ)⁻¹

theorem giantSignedSmallOmissionWeight_total (S : Type*) [Fintype S] [DecidableEq S]
    (kCopy ell : ℕ) :
    (∑ U : GiantSignedSmallOmission S (kCopy + ell) ell,
      giantSignedSmallOmissionWeight S (kCopy + ell) ell U) = 1 := by
  have h : (giantSignedSmallOmissionNumber S (kCopy + ell) ell : ℝ) ≠ 0 := by
    exact_mod_cast (giantSignedSmallOmissionNumber_pos S kCopy ell).ne'
  simp only [giantSignedSmallOmissionWeight, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, giantSignedSmallOmission_card, mul_inv_cancel₀ h]

end
end ArtinMatthews
