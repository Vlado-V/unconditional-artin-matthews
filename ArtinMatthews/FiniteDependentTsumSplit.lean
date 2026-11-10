module

public import Mathlib.Analysis.Complex.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! An absolutely summable dependent product can be split at any coordinate. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

theorem finiteDependentTsum_split {B : Type*} [DecidableEq B]
    (X : B → Type*) (g : B) (f : ((h : B) → X h) → ℂ) (hf : Summable f) :
    (∑' x, f x) =
      ∑' a : X g, ∑' y : (h : {h : B // h ≠ g}) → X h,
        f ((Equiv.piSplitAt g X).symm (a, y)) := by
  let e := Equiv.piSplitAt g X
  have he : Summable (fun z => f (e.symm z)) := (e.symm.summable_iff).mpr hf
  calc
    _ = ∑' z, f (e.symm z) := (e.symm.tsum_eq f).symm
    _ = _ := he.tsum_prod

theorem finiteDependentTsum_split_reverse {B : Type*} [DecidableEq B]
    (X : B → Type*) (g : B) (f : ((h : B) → X h) → ℂ) (hf : Summable f) :
    (∑' x, f x) =
      ∑' y : (h : {h : B // h ≠ g}) → X h, ∑' a : X g,
        f ((Equiv.piSplitAt g X).symm (a, y)) := by
  let e := Equiv.piSplitAt g X
  have he : Summable (fun z => f (e.symm z)) := (e.symm.summable_iff).mpr hf
  calc
    _ = ∑' a : X g, ∑' y : (h : {h : B // h ≠ g}) → X h,
        f (e.symm (a, y)) := finiteDependentTsum_split X g f hf
    _ = _ := he.tsum_comm.symm

end
end ArtinMatthews
