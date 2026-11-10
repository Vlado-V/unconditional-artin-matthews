module

public import Mathlib.Data.Nat.ModEq
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Finset.Nat
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

/-! Exact off-diagonal congruence-pair counts used after the shifted
correlation estimate. The count retains the full spacing parameter. -/
namespace ArtinMatthews
open scoped BigOperators

def shiftedIncreasingPairs (B R : ℕ) : Finset (ℕ×ℕ) :=
  ((Finset.Icc 1 B) ×ˢ (Finset.Icc 1 B)).filter
    (fun p => p.1<p.2 ∧ R∣p.2-p.1)

private theorem shiftedIncreasingPairs_mem {B R : ℕ} {p : ℕ×ℕ} :
    p∈shiftedIncreasingPairs B R ↔
      (1≤p.1 ∧ p.1≤B) ∧ (1≤p.2 ∧ p.2≤B) ∧ p.1<p.2 ∧ R∣p.2-p.1 := by
  simp only [shiftedIncreasingPairs, Finset.mem_filter, Finset.mem_product,
    Finset.mem_Icc]
  tauto

/-- Increasing congruent pairs inject into a first coordinate and a
positive multiple of the spacing; no additive rounding loss remains. -/
theorem shiftedIncreasingPairs_card_le (B R : ℕ) (hR : 0<R) :
    (shiftedIncreasingPairs B R).card ≤ B*(B/R) := by
  let f : ℕ×ℕ → ℕ×ℕ := fun p => (p.1,(p.2-p.1)/R)
  have hf : Set.MapsTo f (shiftedIncreasingPairs B R)
      (((Finset.Icc 1 B) ×ˢ (Finset.Icc 1 (B/R))) : Finset (ℕ×ℕ)) := by
    intro p hp
    obtain ⟨hp1,hp2,hlt,hdvd⟩ := shiftedIncreasingPairs_mem.mp hp
    change f p ∈ ((Finset.Icc 1 B) ×ˢ (Finset.Icc 1 (B/R)))
    simp only [f, Finset.mem_product, Finset.mem_Icc]
    refine ⟨hp1, ?_, Nat.div_le_div_right ((Nat.sub_le p.2 p.1).trans hp2.2)⟩
    exact Nat.div_pos (Nat.le_of_dvd (Nat.sub_pos_of_lt hlt) hdvd) hR
  have hi : Set.InjOn f (shiftedIncreasingPairs B R) := by
    intro p hp q hq heq
    obtain ⟨hp1,hp2,hplt,hpdvd⟩ := shiftedIncreasingPairs_mem.mp hp
    obtain ⟨hq1,hq2,hqlt,hqdvd⟩ := shiftedIncreasingPairs_mem.mp hq
    have hfirst : p.1=q.1 := by simpa only [f] using congrArg Prod.fst heq
    have hquot : (p.2-p.1)/R=(q.2-q.1)/R := by simpa only [f] using congrArg Prod.snd heq
    have hdiff : p.2-p.1=q.2-q.1 := by
      calc
        _ = R*((p.2-p.1)/R) := (Nat.mul_div_cancel' hpdvd).symm
        _ = R*((q.2-q.1)/R) := by rw [hquot]
        _ = _ := Nat.mul_div_cancel' hqdvd
    exact Prod.ext hfirst (by omega)
  have hcard := Finset.card_le_card_of_injOn f hf hi
  simpa only [Finset.card_product, Nat.card_Icc, Nat.add_one_sub_one] using hcard

/-- If the required spacing exceeds the whole interval, there are no
increasing off-diagonal pairs at all. -/
theorem shiftedIncreasingPairs_eq_empty (B R : ℕ) (hBR : B<R) :
    shiftedIncreasingPairs B R=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  obtain ⟨hp1,hp2,hlt,hdvd⟩ := shiftedIncreasingPairs_mem.mp hp
  have hle := Nat.le_of_dvd (Nat.sub_pos_of_lt hlt) hdvd
  omega


/-- All ordered unequal congruent pairs in the interval. -/
def shiftedOffDiagonalPairs (B R : ℕ) : Finset (ℕ×ℕ) :=
  ((Finset.Icc 1 B) ×ˢ (Finset.Icc 1 B)).filter
    (fun p => p.1≠p.2 ∧ Nat.ModEq R p.1 p.2)

theorem shiftedOffDiagonalPairs_card_le (B R : ℕ) (hR : 0<R) :
    (shiftedOffDiagonalPairs B R).card ≤ 2*(B*(B/R)) := by
  have hsub : shiftedOffDiagonalPairs B R ⊆
      shiftedIncreasingPairs B R ∪ (shiftedIncreasingPairs B R).image Prod.swap := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hm,hne,hmod⟩
    rcases Finset.mem_product.mp hm with ⟨hp1,hp2⟩
    rw [Finset.mem_Icc] at hp1 hp2
    by_cases hlt : p.1<p.2
    · exact Finset.mem_union_left _ (shiftedIncreasingPairs_mem.mpr
        ⟨hp1,hp2,hlt,(Nat.modEq_iff_dvd' hlt.le).mp hmod⟩)
    · have hlt' : p.2<p.1 := by omega
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨p.swap,?_,Prod.swap_swap p⟩
      exact shiftedIncreasingPairs_mem.mpr
        ⟨hp2,hp1,hlt',(Nat.modEq_iff_dvd' hlt'.le).mp hmod.symm⟩
  calc
    _ ≤ (shiftedIncreasingPairs B R ∪ (shiftedIncreasingPairs B R).image Prod.swap).card :=
      Finset.card_le_card hsub
    _ ≤ (shiftedIncreasingPairs B R).card+(shiftedIncreasingPairs B R).card :=
      (Finset.card_union_le _ _).trans (Nat.add_le_add_left (Finset.card_image_le) _)
    _ ≤ B*(B/R)+B*(B/R) := Nat.add_le_add
      (shiftedIncreasingPairs_card_le B R hR) (shiftedIncreasingPairs_card_le B R hR)
    _ = _ := by omega

/-- Uniform real-valued form, with the inverse spacing retained. -/
theorem shiftedOffDiagonalPairs_card_real (B R : ℕ) (hR : 0<R) :
    ((shiftedOffDiagonalPairs B R).card : ℝ) ≤ 2*(B : ℝ)^2/(R : ℝ) := by
  have hr : (0 : ℝ)<R := by exact_mod_cast hR
  have hdiv : ((B/R : ℕ) : ℝ) ≤ (B : ℝ)/(R : ℝ) := by
    apply (le_div_iff₀ hr).mpr
    exact_mod_cast Nat.div_mul_le_self B R
  have hc : ((shiftedOffDiagonalPairs B R).card : ℝ) ≤
      2*((B : ℝ)*((B/R : ℕ) : ℝ)) := by
    exact_mod_cast shiftedOffDiagonalPairs_card_le B R hR
  calc
    _ ≤ 2*((B : ℝ)*((B/R : ℕ) : ℝ)) := hc
    _ ≤ 2*((B : ℝ)*((B : ℝ)/(R : ℝ))) := by gcongr
    _ = _ := by ring

end ArtinMatthews
