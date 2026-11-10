module

public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Order.Real
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal


set_option backward.privateInPublic true
@[expose] public section

/-! Tonelli for a finite dependent product of countable rows. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section
universe u v

theorem finiteProduct_tsum_prod {ι : Type u} [Fintype ι]
    (X : ι → Type v) (f : ∀ i, X i → ℝ≥0∞) :
    (∑' x : ∀ i, X i, ∏ i, f i (x i)) = ∏ i, ∑' x : X i, f i x := by
  classical
  revert X f
  refine Fintype.induction_empty_option
    (P := fun ι _ => ∀ (X : ι → Type v) (f : ∀ i, X i → ℝ≥0∞),
      (∑' x : ∀ i, X i, ∏ i, f i (x i)) = ∏ i, ∑' x : X i, f i x) ?_ ?_ ?_ ι
  · intro α β inst e ih X f
    let _ : Fintype α := Fintype.ofEquiv β e.symm
    let pe := Equiv.piCongrLeft X e
    calc
      _ = ∑' x : ∀ a, X (e a), ∏ b, f b (pe x b) := (pe.tsum_eq _).symm
      _ = ∑' x : ∀ a, X (e a), ∏ a, f (e a) (x a) := by
        apply tsum_congr
        intro x
        rw [← e.prod_comp]
        simp only [pe, Equiv.piCongrLeft_apply_apply]
      _ = ∏ a, ∑' x : X (e a), f (e a) x := ih (fun a => X (e a)) (fun a => f (e a))
      _ = _ := e.prod_comp (fun i => ∑' x : X i, f i x)
  · intro X f
    let _ : Unique (∀ i : PEmpty, X i) :=
      ⟨⟨fun i => PEmpty.elim i⟩, fun x => funext fun i => PEmpty.elim i⟩
    simp only [Finset.univ_eq_empty, Finset.prod_empty]
    exact tsum_eq_single default (fun x hx => False.elim (hx (Subsingleton.elim _ _)))
  · intro α inst ih X f
    let pe := Equiv.piOptionEquivProd (β := X)
    have hp (x : X none × (∀ a : α, X (some a))) :
        (∏ i, f i (pe.symm x i)) = f none x.1 * ∏ a, f (some a) (x.2 a) := by
      rw [Fintype.prod_option]
      rfl
    calc
      _ = ∑' x : X none × (∀ a : α, X (some a)), ∏ i, f i (pe.symm x i) :=
        (pe.symm.tsum_eq _).symm
      _ = ∑' a : X none, ∑' x : ∀ i : α, X (some i),
          f none a * ∏ i, f (some i) (x i) := by
        simp_rw [hp]
        exact ENNReal.tsum_prod' (f := fun x : X none × (∀ a : α, X (some a)) =>
          f none x.1 * ∏ a, f (some a) (x.2 a))
      _ = (∑' a : X none, f none a) *
          (∑' x : ∀ i : α, X (some i), ∏ i, f (some i) (x i)) := by
        simp_rw [ENNReal.tsum_mul_left]
        exact ENNReal.tsum_mul_right
      _ = (∑' a : X none, f none a) * ∏ i : α, ∑' x : X (some i), f (some i) x := by
        rw [ih]
      _ = _ := (Fintype.prod_option (fun i => ∑' x : X i, f i x)).symm

end
end ArtinMatthews
