module

public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Fintype.Option
public import Mathlib.Logic.Equiv.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! An absolute finite product of arbitrary local series is the actual
sum over the finite family of local choices. This is the finite-prefix
step for the source Euler product. -/

namespace ArtinMatthews.SourceEuler

open scoped BigOperators Classical

def FinitePiSeriesLaw (I : Type) [Fintype I] (X : Type) : Prop :=
  ∀ f : I → X → ℂ, (∀ i, Summable (fun x => ‖f i x‖)) →
    Summable (fun g : I → X => ‖∏ i, f i (g i)‖) ∧
    (∑' g : I → X, ∏ i, f i (g i)) = ∏ i, ∑' x : X, f i x

theorem finitePiSeriesLaw_equiv {I J : Type} [Fintype I] [Fintype J]
    (X : Type) (e : I ≃ J) (ih : FinitePiSeriesLaw I X) : FinitePiSeriesLaw J X := by
  classical
  intro f hf
  obtain ⟨hs, ht⟩ := ih (fun i => f (e i)) (fun i => hf (e i))
  let d : (I → X) ≃ (J → X) := Equiv.arrowCongr e (Equiv.refl X)
  have hp (g : J → X) :
      (∏ i : I, f (e i) (d.symm g i)) = ∏ j : J, f j (g j) := by
    change (∏ i : I, f (e i) (g (e i))) = _
    exact e.prod_comp (fun j => f j (g j))
  refine ⟨?_, ?_⟩
  · exact ((d.symm.summable_iff).mpr hs).congr (fun g => congrArg norm (hp g))
  · calc
      _ = ∑' g : J → X, ∏ i : I, f (e i) (d.symm g i) := tsum_congr (fun g => (hp g).symm)
      _ = ∑' g : I → X, ∏ i : I, f (e i) (g i) :=
        d.symm.tsum_eq (fun g : I → X => ∏ i : I, f (e i) (g i))
      _ = ∏ i : I, ∑' x : X, f (e i) x := ht
      _ = _ := e.prod_comp (fun j => ∑' x : X, f j x)

theorem finitePiSeriesLaw_empty (X : Type) : FinitePiSeriesLaw PEmpty X := by
  classical
  intro f _hf
  constructor
  · exact (hasSum_fintype _).summable
  · simp

theorem finitePiSeriesLaw_option (I : Type) [Fintype I] (X : Type)
    (ih : FinitePiSeriesLaw I X) : FinitePiSeriesLaw (Option I) X := by
  classical
  intro f hf
  obtain ⟨hs, ht⟩ := ih (fun i => f (some i)) (fun i => hf (some i))
  let e : (Option I → X) ≃ X × (I → X) := Equiv.piOptionEquivProd
  have hp (g : X × (I → X)) :
      (∏ i : Option I, f i (e.symm g i)) =
        f none g.1 * ∏ i : I, f (some i) (g.2 i) := by
    simp only [Fintype.prod_option, e, Equiv.piOptionEquivProd_symm_apply]
  have hn := (hf none).mul_norm hs
  have hnp : Summable (fun g : X × (I → X) => ‖∏ i : Option I, f i (e.symm g i)‖) :=
    hn.congr (fun g => (congrArg norm (hp g)).symm)
  refine ⟨(e.symm.summable_iff).mp hnp, ?_⟩
  calc
    _ = ∑' g : X × (I → X), ∏ i : Option I, f i (e.symm g i) :=
      (e.symm.tsum_eq _).symm
    _ = ∑' g : X × (I → X), f none g.1 * ∏ i : I, f (some i) (g.2 i) :=
      tsum_congr hp
    _ = (∑' x : X, f none x) * (∑' g : I → X, ∏ i : I, f (some i) (g i)) :=
      (tsum_mul_tsum_of_summable_norm (hf none) hs).symm
    _ = _ := by rw [ht, Fintype.prod_option]

theorem finitePiSeries (I : Type) [Fintype I] (X : Type) : FinitePiSeriesLaw I X := by
  apply Fintype.induction_empty_option (P := fun J _ => FinitePiSeriesLaw J X)
  · intro I J _ e ih
    let : Fintype I := Fintype.ofEquiv J e.symm
    exact finitePiSeriesLaw_equiv X e ih
  · exact finitePiSeriesLaw_empty X
  · intro I _ ih
    exact finitePiSeriesLaw_option I X ih

end ArtinMatthews.SourceEuler
