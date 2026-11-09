module

public import Mathlib.Algebra.BigOperators.Associated
public import ArtinMatthews.MarkedEstimateActualModel


set_option backward.privateInPublic true
@[expose] public section

/-! The unshared ordered prime list is recovered from its integer product.
This is the finite arithmetic content of PD04 (mem:product-mass). -/
namespace ArtinMatthews

open scoped BigOperators

/-- A prime occurring in an ordered list of prime factors must match one
of those actual factors. -/
theorem marked_prime_dvd_tuple_product {J : Type*} [Fintype J]
    {p : ℕ} (hp : p.Prime) (s : J → ℕ) (hs : ∀ j, (s j).Prime)
    (hd : p ∣ ∏ j, s j) : ∃ j, p = s j := by
  obtain ⟨j,_,hj⟩ := (hp.prime.dvd_finsetProd_iff s).mp hd
  exact ⟨j, (Nat.prime_dvd_prime_iff_eq hp (hs j)).mp hj⟩

/-- Pairwise disjoint prime bands prevent a matching factor from moving
to any different tuple position. -/
theorem marked_disjoint_prime_tuple_eq_of_product_eq {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (hprime : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    (t s : J → ℕ) (ht : ∀ j, t j ∈ P j) (hs : ∀ j, s j ∈ P j)
    (hprod : (∏ j, t j) = ∏ j, s j) : t = s := by
  classical
  funext i
  have hd : t i ∣ ∏ j, s j := by
    rw [← hprod]
    exact Finset.dvd_prod_of_mem t (Finset.mem_univ i)
  obtain ⟨j,hij⟩ := marked_prime_dvd_tuple_product (hprime i _ (ht i)) s
    (fun j => hprime j _ (hs j)) hd
  have he : i = j := by
    by_contra hne
    exact Finset.disjoint_left.mp (hdis hne) (ht i) (hij.symm ▸ hs j)
  simpa only [← he] using hij

def markedPrimeBandProduct {J : Type*} [Fintype J] (P : J → Finset ℕ)
    (t : (j : J) → ↥(P j)) : ℕ := ∏ j, (t j : ℕ)

/-- The literal product map on the actual dependent ordered prime-list
space is injective, with no permutation quotient. -/
theorem markedPrimeBandProduct_injective {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (hprime : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j))) :
    Function.Injective (markedPrimeBandProduct P) := by
  intro t s hp
  have he := marked_disjoint_prime_tuple_eq_of_product_eq P hprime hdis
    (fun j => (t j : ℕ)) (fun j => (s j : ℕ)) (fun j => (t j).property)
    (fun j => (s j).property) hp
  funext j
  exact Subtype.ext (congrFun he j)

/-- The actual mass pushed forward along the product map has one tuple
in the fiber of each represented product. -/
theorem markedPrimeBandProduct_fiber_mass {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hprime : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    (weight : ((j : J) → ↥(P j)) → ℝ) (t : (j : J) → ↥(P j)) :
    (∑ s, if markedPrimeBandProduct P s = markedPrimeBandProduct P t then weight s else 0) =
      weight t := by
  classical
  rw [Fintype.sum_eq_single t]
  · simp only [ite_true]
  · intro s hst
    have hp : markedPrimeBandProduct P s ≠ markedPrimeBandProduct P t :=
      fun he => hst (markedPrimeBandProduct_injective P hprime hdis he)
    simp only [hp, ite_false]

/-- Distinct actual marking-band exponents eventually give the injective
product coordinate used by the clean minor-arc operator. -/
theorem marked_actual_prime_product_injective_eventually {J : Type*} [Fintype J]
    (e : J → ℝ) (hinj : Function.Injective e) :
    ∀ᶠ x : ℝ in Filter.atTop,
      Function.Injective (markedPrimeBandProduct (fun j => markedLogPowerBand (e j) x)) := by
  filter_upwards [marked_array_disjoint_eventually e hinj] with x hdis
  exact markedPrimeBandProduct_injective _
    (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) hdis

end ArtinMatthews
