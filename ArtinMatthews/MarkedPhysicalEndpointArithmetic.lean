module

public import ArtinMatthews.MarkedPhysicalMarking
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

/-! Exact arithmetic of the full physical lists and their rough cofactors.
In particular the complete band part is recovered from the actual labels,
not assumed equal to their product. -/
noncomputable section
open scoped BigOperators
namespace ArtinMatthews
attribute [local instance] Classical.propDecidable

def markedPhysicalLabelSet {J : Type*} {P : J → Finset ℕ} {M : ℕ}
    (a : MarkedPhysicalMarking P M) (j : J) : Finset ℕ :=
  Finset.univ.image (fun k => (a j k : ℕ))

theorem markedPhysicalLabelSet_subset {J : Type*} {P : J → Finset ℕ} {M : ℕ}
    (a : MarkedPhysicalMarking P M) (j : J) : markedPhysicalLabelSet a j ⊆ P j := by
  intro p hp
  obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hp
  exact (a j k).2

theorem markedPhysicalLabelSet_card {J : Type*} {P : J → Finset ℕ} {M : ℕ}
    (a : MarkedPhysicalMarking P M) (ha : MarkedPhysicalMarkingDistinct a) (j : J) :
    (markedPhysicalLabelSet a j).card = M := by
  rw [markedPhysicalLabelSet, Finset.card_image_of_injective]
  · exact Fintype.card_fin M
  · exact Subtype.val_injective.comp (ha j)

theorem markedPhysicalMarkingProduct_pos {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hP : ∀ j p, p ∈ P j → p.Prime) {M : ℕ}
    (a : MarkedPhysicalMarking P M) : 0 < markedPhysicalMarkingProduct a :=
  Finset.prod_pos (fun j _ => Finset.prod_pos (fun k _ => (hP j _ (a j k).2).pos))

theorem markedPhysicalMarkingProduct_prime_dvd_iff {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hP : ∀ j p, p ∈ P j → p.Prime) {M : ℕ}
    (a : MarkedPhysicalMarking P M) {p : ℕ} (hp : p.Prime) :
    p ∣ markedPhysicalMarkingProduct a ↔ ∃ j k, p = (a j k : ℕ) := by
  simp only [markedPhysicalMarkingProduct, hp.prime.dvd_finsetProd_iff,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, k, h⟩
    exact ⟨j, k, (((hP j _ (a j k).2).dvd_iff_eq hp.ne_one).mp h).symm⟩
  · rintro ⟨j, k, rfl⟩
    exact ⟨j, k, dvd_rfl⟩

theorem markedPhysicalMarking_global_injective {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hdis : Pairwise (fun j l => Disjoint (P j) (P l)))
    {M : ℕ} (a : MarkedPhysicalMarking P M) (ha : MarkedPhysicalMarkingDistinct a) :
    Function.Injective (fun t : J × Fin M => (a t.1 t.2 : ℕ)) := by
  rintro ⟨j, k⟩ ⟨l, h⟩ heq
  have hjl : j = l := by
    by_contra hn
    exact Finset.disjoint_left.mp (hdis hn) (a j k).2 (by simpa only [heq] using (a l h).2)
  subst l
  have hkh : k = h := ha j (Subtype.ext heq)
  subst h
  rfl

theorem markedPhysicalMarkingProduct_squarefree {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun j l => Disjoint (P j) (P l)))
    {M : ℕ} (a : MarkedPhysicalMarking P M) (ha : MarkedPhysicalMarkingDistinct a) :
    Squarefree (markedPhysicalMarkingProduct a) := by
  classical
  have hi := markedPhysicalMarking_global_injective hdis a ha
  rw [markedPhysicalMarkingProduct, ← Fintype.prod_prod_type (fun t : J × Fin M => (a t.1 t.2 : ℕ))]
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro i _ j _ hij
    apply Nat.coprime_iff_isRelPrime.mp
    exact (Nat.coprime_primes (hP _ _ (a i.1 i.2).2) (hP _ _ (a j.1 j.2).2)).mpr
      (fun h => hij (hi h))
  · intro i _
    exact (hP _ _ (a i.1 i.2).2).squarefree

/-- The exact roughness property used here; no primality of the cofactor
and no restriction on its non-band prime powers is imposed. -/
def MarkedPhysicalBandRough {J : Type*} (P : J → Finset ℕ) (m : ℕ) : Prop :=
  ∀ j p, p ∈ P j → ¬p ∣ m

theorem markedPhysical_activeDivisors_mul {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun j l => Disjoint (P j) (P l)))
    {M : ℕ} (a : MarkedPhysicalMarking P M) {m : ℕ} (hm : MarkedPhysicalBandRough P m)
    (j : J) : activeDivisors (P j) (markedPhysicalMarkingProduct a * m) =
      markedPhysicalLabelSet a j := by
  ext p
  simp only [activeDivisors, Finset.mem_filter, markedPhysicalLabelSet,
    Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hp, hd⟩
    have hdG := ((hP j p hp).dvd_mul.mp hd).resolve_right (hm j p hp)
    obtain ⟨l, k, heq⟩ := (markedPhysicalMarkingProduct_prime_dvd_iff hP a (hP j p hp)).mp hdG
    have hjl : j = l := by
      by_contra hn
      exact Finset.disjoint_left.mp (hdis hn) hp (heq ▸ (a l k).2)
    subst l
    exact ⟨k, heq.symm⟩
  · rintro ⟨k, rfl⟩
    exact ⟨(a j k).2, dvd_mul_of_dvd_left
      ((markedPhysicalMarkingProduct_prime_dvd_iff hP a (hP j _ (a j k).2)).mpr ⟨j, k, rfl⟩) m⟩

/-- On the endpoint support this is the complete squarefree band-supported
part, retaining the original group decomposition. -/
def markedPhysicalSupportedProduct {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (u : ℕ) : ℕ := ∏ j, ∏ p ∈ activeDivisors (P j) u, p

def MarkedPhysicalEndpointSupport {J : Type*} (P : J → Finset ℕ) (M u : ℕ) : Prop :=
  (∀ j, bandCount (P j) u = M) ∧ (∀ j p, p ∈ P j → ¬p ^ 2 ∣ u)

theorem markedPhysicalSupportedProduct_mul {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun j l => Disjoint (P j) (P l)))
    {M : ℕ} (a : MarkedPhysicalMarking P M) (ha : MarkedPhysicalMarkingDistinct a)
    {m : ℕ} (hm : MarkedPhysicalBandRough P m) :
    markedPhysicalSupportedProduct P (markedPhysicalMarkingProduct a * m) =
      markedPhysicalMarkingProduct a := by
  unfold markedPhysicalSupportedProduct markedPhysicalMarkingProduct
  apply Finset.prod_congr rfl
  intro j _
  change (∏ p ∈ activeDivisors (P j) (markedPhysicalMarkingProduct a * m), p) = _
  rw [markedPhysical_activeDivisors_mul hP hdis a hm j]
  exact Finset.prod_image (fun k _ l _ hkl => ha j (Subtype.ext hkl))

theorem markedPhysicalEndpointSupport_mul {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun j l => Disjoint (P j) (P l)))
    {M : ℕ} (a : MarkedPhysicalMarking P M) (ha : MarkedPhysicalMarkingDistinct a)
    {m : ℕ} (hm : MarkedPhysicalBandRough P m) :
    MarkedPhysicalEndpointSupport P M (markedPhysicalMarkingProduct a * m) := by
  refine ⟨?_, ?_⟩
  · intro j
    rw [bandCount, markedPhysical_activeDivisors_mul hP hdis a hm j]
    exact markedPhysicalLabelSet_card a ha j
  · intro j p hp hd
    apply hm j p hp
    apply (markedPhysicalMarkingProduct_squarefree hP hdis a ha).dvd_of_squarefree_of_mul_dvd_mul_right
    simpa [pow_two] using hd

theorem markedPhysical_quotient_mul {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun j l => Disjoint (P j) (P l)))
    {M : ℕ} (a : MarkedPhysicalMarking P M) (ha : MarkedPhysicalMarkingDistinct a)
    {m : ℕ} (hm : MarkedPhysicalBandRough P m) :
    markedPhysicalMarkingProduct a * m /
      markedPhysicalSupportedProduct P (markedPhysicalMarkingProduct a * m) = m := by
  rw [markedPhysicalSupportedProduct_mul hP hdis a ha hm]
  exact Nat.mul_div_right _ (markedPhysicalMarkingProduct_pos hP a)

end ArtinMatthews
