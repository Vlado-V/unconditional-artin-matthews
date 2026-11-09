module

public import ArtinMatthews.MarkedMinorArcRawEdgePatternAction
public import ArtinMatthews.MarkedMinorArcRawEdgeBranches


set_option backward.privateInPublic true
@[expose] public section

/-! Exact disjoint partition of literal edge flags.  The full dirty
complement includes pure storage, pure promotion, disjoint nonempty flags,
and overlapping flags; none of these sectors is silently discarded. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

inductive MarkedRawEdgeSector where
  | clean | storeOnly | promoteOnly | disjoint | overlap
  deriving DecidableEq

instance : Fintype MarkedRawEdgeSector where
  elems := {.clean, .storeOnly, .promoteOnly, .disjoint, .overlap}
  complete k := by cases k <;> simp

def MarkedRawEdgeFlagsOverlap {J : Type*} (p q : J → Bool) : Prop :=
  ∃ j, p j = true ∧ q j = true

def markedRawEdgeClassify {J : Type*} (p q : J → Bool) : MarkedRawEdgeSector :=
  if p = fun _ => false then
    if q = fun _ => false then .clean else .storeOnly
  else if q = fun _ => false then .promoteOnly
  else if MarkedRawEdgeFlagsOverlap p q then .overlap else .disjoint

def markedRawEdgeSectorSwap : MarkedRawEdgeSector → MarkedRawEdgeSector
  | .storeOnly => .promoteOnly
  | .promoteOnly => .storeOnly
  | k => k

@[simp] theorem markedRawEdgeSectorSwap_swap (k : MarkedRawEdgeSector) :
    markedRawEdgeSectorSwap (markedRawEdgeSectorSwap k) = k := by cases k <;> rfl

theorem markedRawEdgeFlagsOverlap_swap {J : Type*} (p q : J → Bool) :
    MarkedRawEdgeFlagsOverlap p q ↔ MarkedRawEdgeFlagsOverlap q p := by
  constructor <;> rintro ⟨j,hp,hq⟩ <;> exact ⟨j,hq,hp⟩

theorem markedRawEdgeClassify_swap {J : Type*} (p q : J → Bool) :
    markedRawEdgeClassify q p = markedRawEdgeSectorSwap (markedRawEdgeClassify p q) := by
  by_cases hp : p = fun _ => false <;> by_cases hq : q = fun _ => false
  · simp [markedRawEdgeClassify,hp,hq,markedRawEdgeSectorSwap]
  · simp [markedRawEdgeClassify,hp,hq,markedRawEdgeSectorSwap]
  · simp [markedRawEdgeClassify,hp,hq,markedRawEdgeSectorSwap]
  · by_cases ho : MarkedRawEdgeFlagsOverlap p q
    · have hr := (markedRawEdgeFlagsOverlap_swap p q).mp ho
      simp [markedRawEdgeClassify,hp,hq,ho,hr,markedRawEdgeSectorSwap]
    · have hr := mt (markedRawEdgeFlagsOverlap_swap p q).mpr ho
      simp [markedRawEdgeClassify,hp,hq,ho,hr,markedRawEdgeSectorSwap]

theorem markedRawEdgeClassify_clean_iff {J : Type*} (p q : J → Bool) :
    markedRawEdgeClassify p q = .clean ↔ (p = fun _ => false) ∧ (q = fun _ => false) := by
  unfold markedRawEdgeClassify
  split_ifs <;> simp_all

theorem markedRawEdgeChoiceClean_iff_sector {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    {hZ : ∀ z ∈ Z, IsCoprime z.1 z.2} {s : MarkedRawState P (pads+1) B Z}
    (c : MarkedRawEdgeChoice hZ s) :
    MarkedRawEdgeChoiceClean c ↔ markedRawEdgeClassify (markedRawEdgeChoicePromoted c) c.store = .clean := by
  rw [markedRawEdgeClassify_clean_iff]
  constructor
  · intro h
    constructor
    · funext j
      simp only [markedRawEdgeChoicePromoted,h.2 j,Option.isSome_none]
    · exact funext h.1
  · rintro ⟨hp,hq⟩
    constructor
    · intro j
      exact congrFun hq j
    · intro j
      have h := congrFun hp j
      change (c.promotions j).isSome = false at h
      cases he : c.promotions j <;> simp_all

def markedRawEdgeSectorKernel {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (k : MarkedRawEdgeSector) (A : MarkedRawEdgePatternKernel P pads B Z) :
    MarkedRawEdgePatternKernel P pads B Z :=
  fun p q s t => if markedRawEdgeClassify p q = k then A p q s t else 0

theorem markedRawEdgeSectorKernel_sum {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (A : MarkedRawEdgePatternKernel P pads B Z) (p q : J → Bool)
    (s t : MarkedRawState P (pads+1) B Z) :
    (∑ k : MarkedRawEdgeSector, markedRawEdgeSectorKernel k A p q s t) = A p q s t := by
  simp [markedRawEdgeSectorKernel]

theorem markedRawEdgeSectorKernel_reverse {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (k : MarkedRawEdgeSector) (A : MarkedRawEdgePatternKernel P pads B Z) :
    markedRawEdgePatternReverse (markedRawEdgeSectorKernel k A) =
      markedRawEdgeSectorKernel (markedRawEdgeSectorSwap k) (markedRawEdgePatternReverse A) := by
  funext p q s t
  have hh : markedRawEdgeClassify q p = k ↔
      markedRawEdgeClassify p q = markedRawEdgeSectorSwap k := by
    rw [markedRawEdgeClassify_swap]
    constructor
    · intro h
      simpa only [markedRawEdgeSectorSwap_swap] using congrArg markedRawEdgeSectorSwap h
    · intro h
      simpa only [markedRawEdgeSectorSwap_swap] using congrArg markedRawEdgeSectorSwap h
  simp only [markedRawEdgePatternReverse,markedRawEdgeSectorKernel,hh]

theorem markedRawEdgePatternApply_sector_sum {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (δ γ : J → ℂ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (A : MarkedRawEdgePatternKernel P pads B Z)
    (f : MarkedRawState P (pads+1) B Z → ℂ) (s : MarkedRawState P (pads+1) B Z) :
    markedRawEdgePatternApply ν δ γ hZ A f s =
      ∑ k : MarkedRawEdgeSector, markedRawEdgePatternApply ν δ γ hZ (markedRawEdgeSectorKernel k A) f s := by
  unfold markedRawEdgePatternApply
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  rw [markedRawEdgeSectorKernel_sum]

end
end ArtinMatthews
