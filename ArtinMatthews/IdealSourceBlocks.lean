module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
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

/-! Balanced finite blocks and their literal first-slot probe sets
have the source cardinalities uniformly over growing group carriers. -/
namespace ArtinMatthews
open Finset Filter
open scoped BigOperators Topology
noncomputable section
attribute [local instance] Classical.propDecidable

def idealSourceFirstSlots {m J : ℕ} (hm : m ≤ J) : Finset (Fin J) :=
  (univ : Finset (Fin m)).map (Fin.castLEEmb hm)

theorem idealSourceFirstSlots_mem {m J : ℕ} (hm : m ≤ J) (i : Fin J) :
    i ∈ idealSourceFirstSlots hm ↔ i.val < m := by
  unfold idealSourceFirstSlots
  constructor
  · intro hi
    obtain ⟨k, _, hk⟩ := mem_map.mp hi
    have hv := congrArg Fin.val hk
    change k.val = i.val at hv
    exact hv ▸ k.isLt
  · intro hi
    refine mem_map.mpr ⟨⟨i.val, hi⟩, mem_univ _, ?_⟩
    apply Fin.ext
    rfl

theorem idealSourceFirstSlots_card {m J : ℕ} (hm : m ≤ J) :
    (idealSourceFirstSlots hm).card = m := by
  simp only [idealSourceFirstSlots, card_map, card_univ, Fintype.card_fin]

def idealSourceProbes {G : Type*} (S : Finset G) {m J : ℕ} (hm : m ≤ J) :
    Finset (G × Fin J) := S ×ˢ idealSourceFirstSlots hm

theorem idealSourceProbes_mem {G : Type*} (S : Finset G) {m J : ℕ} (hm : m ≤ J)
    (g : G) (i : Fin J) : (g,i) ∈ idealSourceProbes S hm ↔ g ∈ S ∧ i.val < m := by
  simp only [idealSourceProbes, mem_product, idealSourceFirstSlots_mem]

theorem idealSourceProbes_card {G : Type*} (S : Finset G) {m J : ℕ} (hm : m ≤ J) :
    (idealSourceProbes S hm).card = m*S.card := by
  rw [idealSourceProbes, card_product, idealSourceFirstSlots_card, Nat.mul_comm]

theorem idealSourceProbes_disjoint {G : Type*} [DecidableEq G] (S T : Finset G)
    {m J : ℕ} (hm : m ≤ J) (hST : Disjoint S T) :
    Disjoint (idealSourceProbes S hm) (idealSourceProbes T hm) := by
  apply disjoint_left.mpr
  intro z hzS hzT
  exact disjoint_left.mp hST (mem_product.mp hzS).1 (mem_product.mp hzT).1

theorem idealSourceProbes_total_card {G : Type*} [DecidableEq G] (S T U : Finset G)
    {m J : ℕ} (hm : m ≤ J) (hST : Disjoint S T) (hU : S ∪ T = U) :
    (idealSourceProbes S hm).card+(idealSourceProbes T hm).card = m*U.card := by
  rw [idealSourceProbes_card, idealSourceProbes_card, ← Nat.mul_add,
    ← card_union_of_disjoint hST, hU]

theorem idealSource_balanced_partition {G : Type*} [DecidableEq G] (U : Finset G) :
    ∃ S T : Finset G, Disjoint S T ∧ S ∪ T = U ∧
      S.card = U.card/2 ∧ T.card = U.card-U.card/2 := by
  obtain ⟨S, hSU, hS⟩ := exists_subset_card_eq (s := U) (n := U.card/2) (Nat.div_le_self _ _)
  refine ⟨S, U \ S, ?_, ?_, hS, ?_⟩
  · apply disjoint_left.mpr
    intro x hx hxs
    exact (mem_sdiff.mp hxs).2 hx
  · exact union_sdiff_of_subset hSU
  · rw [card_sdiff_of_subset hSU, hS]

theorem idealSource_half_block_lower (b : ℕ) {t : ℝ} (ht : 3 ≤ t) (hb : t ≤ (b : ℝ)) :
    t/3 ≤ ((b/2 : ℕ) : ℝ) ∧ t/3 ≤ ((b-b/2 : ℕ) : ℝ) := by
  have hfloor : b ≤ 2*(b/2)+1 := by omega
  have hfloorR : (b : ℝ) ≤ 2*((b/2 : ℕ) : ℝ)+1 := by exact_mod_cast hfloor
  have hhalf : b/2 ≤ b-b/2 := by omega
  have hhalfR : ((b/2 : ℕ) : ℝ) ≤ ((b-b/2 : ℕ) : ℝ) := by exact_mod_cast hhalf
  constructor <;> nlinarith

universe u

theorem idealSource_balanced_blocks_eventually (c₀ : ℝ) (hc₀ : 0 < c₀) :
    ∀ᶠ L : ℝ in atTop, ∀ (G : Type u) [DecidableEq G] (U : Finset G),
      c₀*Real.log L ≤ U.card →
      ∃ S T : Finset G, Disjoint S T ∧ S ∪ T = U ∧
        c₀*Real.log L/3 ≤ S.card ∧ c₀*Real.log L/3 ≤ T.card := by
  filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (3/c₀))] with L hL
  have ht : 3 ≤ c₀*Real.log L := by
    have h := (div_le_iff₀ hc₀).mp hL
    nlinarith
  intro G _ U hU
  obtain ⟨S,T,hST,hunion,hS,hT⟩ := idealSource_balanced_partition U
  have hcard := idealSource_half_block_lower U.card ht hU
  exact ⟨S,T,hST,hunion,by simpa only [hS] using hcard.1,by simpa only [hT] using hcard.2⟩

end
end ArtinMatthews
