module

public import ArtinMatthews.MarkedFiniteProductAverage
public import ArtinMatthews.MarkedMemoryIndependentLineExpectation


set_option backward.privateInPublic true
@[expose] public section

/-! Exact marginalization of a finite uniform line tuple. Unselected
coordinates are averaged out; an arbitrary observable of all selected
coordinates, including coupled repeated visits, remains unchanged. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators

def markedFiniteSubsetPiRestrict {α : Type*} [DecidableEq α]
    {s t : Finset α} (hst : s ⊆ t) (F : α → Type*)
    (ell : (p : t) → F p.1) : (p : s) → F p.1 :=
  fun p => ell ⟨p.1,hst p.2⟩

def markedFiniteSubsetPiEquiv {α : Type*} [DecidableEq α]
    (s t : Finset α) (hst : s ⊆ t) (F : α → Type*) :
    ((p : t) → F p.1) ≃ ((p : s) → F p.1) × ((p : ↥(t \ s)) → F p.1) where
  toFun ell := (markedFiniteSubsetPiRestrict hst F ell,
    fun p => ell ⟨p.1,(Finset.mem_sdiff.mp p.2).1⟩)
  invFun ell p := if hp : p.1 ∈ s then ell.1 ⟨p.1,hp⟩
    else ell.2 ⟨p.1,Finset.mem_sdiff.mpr ⟨p.2,hp⟩⟩
  left_inv ell := by
    funext p
    dsimp only [markedFiniteSubsetPiRestrict]
    split_ifs <;> rfl
  right_inv := by
    rintro ⟨ell,other⟩
    apply Prod.ext
    · funext p
      dsimp only [markedFiniteSubsetPiRestrict]
      simp only [dite_eq_left p.2]
    · funext p
      simp only [dite_eq_right (Finset.mem_sdiff.mp p.2).2]

theorem marked_finite_subset_pi_mean {α : Type*} [DecidableEq α]
    (s t : Finset α) (hst : s ⊆ t) (F : α → Type*)
    [∀ p,Fintype (F p)] [∀ p,Nonempty (F p)]
    (f : ((p : s) → F p.1) → ℝ) :
    (∑ ell : (p : t) → F p.1,f (markedFiniteSubsetPiRestrict hst F ell))/
        (Fintype.card ((p : t) → F p.1):ℝ) =
      (∑ ell : (p : s) → F p.1,f ell)/(Fintype.card ((p : s) → F p.1):ℝ) := by
  let e := markedFiniteSubsetPiEquiv s t hst F
  have hsum : (∑ ell : (p : t) → F p.1,f (markedFiniteSubsetPiRestrict hst F ell)) =
      (∑ ell : (p : s) → F p.1,f ell)*(Fintype.card ((p : ↥(t \ s)) → F p.1):ℝ) := by
    calc
      _ = ∑ pair : ((p : s) → F p.1) × ((p : ↥(t \ s)) → F p.1),f pair.1 :=
        Equiv.sum_comp e (fun pair => f pair.1)
      _ = _ := by
        rw [Fintype.sum_prod_type]
        simp only [Finset.sum_const,nsmul_eq_mul]
        rw [← Finset.mul_sum,mul_comm,Finset.card_univ]
  have hcard : Fintype.card ((p : t) → F p.1) =
      Fintype.card ((p : s) → F p.1)*Fintype.card ((p : ↥(t \ s)) → F p.1) :=
    (Fintype.card_congr e).trans (Fintype.card_prod _ _)
  rw [hsum,hcard,Nat.cast_mul]
  exact mul_div_mul_right _ _ (by exact_mod_cast Fintype.card_ne_zero)

theorem markedMemoryIndependentLines_marginal (s t : Finset Nat.Primes) (hst : s ⊆ t)
    (f : MarkedMemoryIndependentLines s → ℝ) :
    (∑ ell : MarkedMemoryIndependentLines t,
        f (markedFiniteSubsetPiRestrict hst MarkedRawPrimeLine ell))/
        (Fintype.card (MarkedMemoryIndependentLines t):ℝ) =
      (∑ ell : MarkedMemoryIndependentLines s,f ell)/
        (Fintype.card (MarkedMemoryIndependentLines s):ℝ) := by
  let (p : Nat.Primes) : Nonempty (MarkedRawPrimeLine p) := ⟨markedVerticalProjectiveLine _⟩
  exact marked_finite_subset_pi_mean s t hst MarkedRawPrimeLine f

end ArtinMatthews
