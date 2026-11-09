module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Antidiag.Nat
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Tactic


set_option backward.privateInPublic true
@[expose] public section

/-! The finite ordered positive factor tuples with their original product
cutoff. Selecting one slot leaves an exact ordered cofactor fiber. -/

namespace ArtinMatthews
open Finset
open scoped BigOperators

def giantOrderedProductTuples (k X : ℕ) : Finset (Fin k → ℕ) :=
  (Fintype.piFinset (fun _ : Fin k => Ioc 0 X)).filter (fun t => (∏ i,t i) ≤ X)

abbrev giantOrderedProductFiber (k n : ℕ) : Finset (Fin k → ℕ) :=
  Nat.finMulAntidiag k n

theorem mem_giantOrderedProductTuples {k X : ℕ} {t : Fin k → ℕ} :
    t ∈ giantOrderedProductTuples k X ↔ (∀ i, 0 < t i) ∧ (∏ i,t i) ≤ X := by
  rw [giantOrderedProductTuples,mem_filter,Fintype.mem_piFinset]
  constructor
  · exact fun h => ⟨fun i => (mem_Ioc.mp (h.1 i)).1,h.2⟩
  · rintro ⟨ht,hX⟩
    have hprod : 0 < ∏ i,t i := prod_pos (fun i _ => ht i)
    refine ⟨fun i => mem_Ioc.mpr ⟨ht i,?_⟩,hX⟩
    exact (Nat.le_of_dvd hprod (dvd_prod_of_mem t (mem_univ i))).trans hX

theorem mem_giantOrderedProductFiber {k n : ℕ} {t : Fin k → ℕ} :
    t ∈ giantOrderedProductFiber k n ↔ (∀ i, 0 < t i) ∧ (∏ i,t i) = n := by
  constructor
  · intro ht
    exact ⟨fun i => Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_finMulAntidiag ht i),
      (Nat.mem_finMulAntidiag.mp ht).1⟩
  · rintro ⟨ht,hprod⟩
    exact Nat.mem_finMulAntidiag.mpr ⟨hprod,hprod ▸ (prod_pos (fun i _ => ht i)).ne'⟩

theorem giantOrderedProductFiber_filter {k n X : ℕ} (hn : n ≤ X) :
    (giantOrderedProductTuples k X).filter (fun t => (∏ i,t i) = n) =
      giantOrderedProductFiber k n := by
  ext t
  rw [mem_filter,mem_giantOrderedProductTuples,mem_giantOrderedProductFiber]
  exact ⟨fun h => ⟨h.1.1,h.2⟩,fun h => ⟨⟨h.1,h.2.le.trans hn⟩,h.2⟩⟩

theorem giant_insertNth_pos {k : ℕ} (i : Fin (k+1)) {m : ℕ} {t : Fin k → ℕ}
    (hm : 0 < m) (ht : ∀ j, 0 < t j) :
    ∀ j, 0 < Fin.insertNth (α := fun _ => ℕ) i m t j := by
  intro j
  rcases eq_or_ne j i with rfl | hne
  · simpa only [Fin.insertNth_apply_same] using hm
  · obtain ⟨l,rfl⟩ := Fin.exists_succAbove_eq_iff.mpr hne
    simpa only [Fin.insertNth_apply_succAbove] using ht l

theorem giant_ordered_product_tuple_sum_split {A : Type*} [AddCommMonoid A]
    (k X : ℕ) (i : Fin (k+1)) (F : ℕ → (Fin k → ℕ) → A) :
    (∑ t ∈ giantOrderedProductTuples (k+1) X, F (t i) (i.removeNth t)) =
      ∑ mn ∈ ((Ioc 0 X)×ˢ(Ioc 0 X)).filter (fun mn => mn.1*mn.2 ≤ X),
        ∑ u ∈ giantOrderedProductFiber k mn.2, F mn.1 u := by
  classical
  let R := ((Ioc 0 X)×ˢ(Ioc 0 X)).filter (fun mn => mn.1*mn.2 ≤ X)
  let fiber (mn : ℕ×ℕ) := giantOrderedProductFiber k mn.2
  let f (t : Fin (k+1) → ℕ) : Σ _ : ℕ×ℕ, Fin k → ℕ :=
    ⟨(t i,∏ j,i.removeNth t j),i.removeNth t⟩
  change _ = ∑ mn ∈ R, ∑ u ∈ fiber mn, F mn.1 u
  rw [← sum_sigma R fiber (fun p => F p.1.1 p.2)]
  apply sum_bij (fun t _ => f t)
  · intro t ht
    obtain ⟨hp,hX⟩ := mem_giantOrderedProductTuples.mp ht
    let u := i.removeNth t
    let n := ∏ j,u j
    have hu (j : Fin k) : 0 < u j := hp (i.succAbove j)
    have hn : 0 < n := prod_pos (fun j _ => hu j)
    have hmn : t i*n ≤ X := (Fin.mul_prod_removeNth i t).trans_le hX
    have hpos : 0 < t i*n := Nat.mul_pos (hp i) hn
    have hmX : t i ≤ X := (Nat.le_of_dvd hpos ⟨n,rfl⟩).trans hmn
    have hnX : n ≤ X := (Nat.le_of_dvd hpos ⟨t i,Nat.mul_comm _ _⟩).trans hmn
    exact mem_sigma.mpr ⟨mem_filter.mpr ⟨mem_product.mpr
      ⟨mem_Ioc.mpr ⟨hp i,hmX⟩,mem_Ioc.mpr ⟨hn,hnX⟩⟩,hmn⟩,
      mem_giantOrderedProductFiber.mpr ⟨hu,rfl⟩⟩
  · intro t _ v _ h
    have he := congrArg (fun p : Σ _ : ℕ×ℕ, Fin k → ℕ =>
      Fin.insertNth (α := fun _ => ℕ) i p.1.1 p.2) h
    simpa only [f,Fin.insertNth_self_removeNth] using he
  · rintro ⟨⟨m,n⟩,u⟩ h
    obtain ⟨hmn,hu⟩ := mem_sigma.mp h
    obtain ⟨hbox,hprod⟩ := mem_filter.mp hmn
    obtain ⟨hupos,hun⟩ := mem_giantOrderedProductFiber.mp hu
    have hm := (mem_Ioc.mp (mem_product.mp hbox).1).1
    let t := Fin.insertNth (α := fun _ => ℕ) i m u
    refine ⟨t,mem_giantOrderedProductTuples.mpr ⟨giant_insertNth_pos i hm hupos,?_⟩,?_⟩
    · simpa only [t,Fin.prod_insertNth,hun] using hprod
    · simp only [f,t,Fin.insertNth_apply_same,Fin.removeNth_insertNth,hun]
  · intro t _
    rfl

end ArtinMatthews
