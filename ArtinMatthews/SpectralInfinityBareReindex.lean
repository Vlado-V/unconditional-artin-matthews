module

public import ArtinMatthews.SpectralInfinityBareFibre
public import ArtinMatthews.SpectralABLSameCuspBareReindex


set_option backward.privateInPublic true
@[expose] public section

/-! The native infinity bare series uses the literal ordinary summand
on the positive multiples of N. -/

noncomputable section
open Set
open scoped MatrixGroups

namespace ArtinMatthews

theorem gamma0Infinity_bareFibre_index (N : ℕ) [NeZero N] (k : ℕ) (n : ℤ) (H : ℂ → ℂ) :
    gamma0TrueWidthBareFibre N 1 1 (gamma0AtkinSameCuspIndex N k) n n H =
      gamma0AtkinSameCuspBareSummand N n H k := by
  rw [gamma0Infinity_bareFibre_eq_oneOver]
  simpa only [one_mul] using gamma0AtkinSameCusp_bareFibre_index 1 N (Nat.coprime_one_left N) k n H

theorem gamma0Infinity_bareSeries_reindex_summable (N : ℕ) [NeZero N] (n : ℤ) (H : ℂ → ℂ) :
    let f (c : Ioi (0 : ℕ)) := gamma0TrueWidthBareFibre N 1 1 c n n H
    (Summable f ↔ Summable (gamma0AtkinSameCuspBareSummand N n H)) ∧
      (∑' c, f c) = ∑' k, gamma0AtkinSameCuspBareSummand N n H k := by
  let f (c : Ioi (0 : ℕ)) := gamma0TrueWidthBareFibre N 1 1 c n n H
  let e := gamma0AtkinSameCuspIndex N
  change (Summable f ↔ Summable _) ∧ (∑' c, f c) = _
  have hzero (c : Ioi (0 : ℕ)) (hc : c ∉ range e) : f c = 0 :=
    gamma0Infinity_bareFibre_zero N c
      (fun hd => hc ((gamma0AtkinSameCuspIndex_range N c).mpr hd)) n H
  have he : f ∘ e = gamma0AtkinSameCuspBareSummand N n H :=
    funext (fun k => gamma0Infinity_bareFibre_index N k n H)
  have hs := e.injective.summable_iff (f := f) hzero
  rw [he] at hs
  refine ⟨hs.symm, ?_⟩
  have hsupport : Function.support f ⊆ range e := fun c hc =>
    by_contradiction (fun h => hc (hzero c h))
  calc
    _ = ∑' k, (f ∘ e) k := (e.injective.tsum_eq hsupport).symm
    _ = _ := congrArg tsum he

theorem gamma0Infinity_bareSeries_reindex (N : ℕ) [NeZero N] (n : ℤ) (H : ℂ → ℂ) :
    (∑' c : Ioi (0 : ℕ), gamma0TrueWidthBareFibre N 1 1 c n n H) =
      ∑' k, gamma0AtkinSameCuspBareSummand N n H k :=
  (gamma0Infinity_bareSeries_reindex_summable N n H).2

end ArtinMatthews
