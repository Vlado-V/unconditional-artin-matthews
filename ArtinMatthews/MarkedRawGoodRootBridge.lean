module

public import ArtinMatthews.MarkedPhysicalBadRootEnergy
public import ArtinMatthews.MarkedMinorArcDirtyGoodCutoff


set_option backward.privateInPublic true
@[expose] public section

/-! The conditional circle event is the actual good test at the canonical
source root. Away from that root the precise transported ratio remains
visible; no equidistribution assertion is inserted. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem markedRawDirtyGood_iff_not_badRootSet
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x r d₀ Y : ℝ) {B : ℕ} {Z : Finset (ℤ × ℤ)}
    (w : Z → ℤ × ℤ)
    (s : MarkedRawState (markedRawActualPrimeBand e x) (markedPadSlots x) B Z) :
    MarkedRawDirtyGood e x r d₀ Y w s ↔
      ((markedMinorIntegerTau r (w s.1)/markedMinorIntegerTau r s.1.1:ℝ):AddCircle (1:ℝ)) ∉
        markedRawBadRootSet e x d₀ Y s.2.1 := by
  rw [MarkedRawDirtyGood,markedRawDirtySecondGood_iff_not_bad]
  simp only [markedRawBadRootSet,Set.mem_union,not_or,MarkedRawFirstGood,markedRawFirstBadRootSet]

theorem markedRawRootBadBoundary_eq_actual_bad
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x r d₀ Y : ℝ) {B : ℕ} {Z : Finset (ℤ × ℤ)}
    (w : Z → ℤ × ℤ) (z₀ : Z) (hz₀ : z₀.1 = (1,0)) (hw : w z₀ = (0,1))
    (s : MarkedRawState (markedRawActualPrimeBand e x) (markedPadSlots x) B Z) :
    markedRawRootBadBoundary e x d₀ Y z₀ (r:AddCircle (1:ℝ)) s =
      if MarkedRawDirtyGood e x r d₀ Y w s then 0 else markedRawBoundary z₀ s := by
  by_cases hz : s.1 = z₀
  · have hratio : markedMinorIntegerTau r (w s.1)/markedMinorIntegerTau r s.1.1 = r := by
      simp [hz,hw,hz₀,markedMinorIntegerTau]
    have hg := markedRawDirtyGood_iff_not_badRootSet e x r d₀ Y w s
    rw [hratio] at hg
    by_cases hb : (r:AddCircle (1:ℝ)) ∈ markedRawBadRootSet e x d₀ Y s.2.1
    · have hng : ¬MarkedRawDirtyGood e x r d₀ Y w s := by
        intro h
        exact (hg.mp h) hb
      simp [markedRawRootBadBoundary,hb,hng]
    · have hgood := hg.mpr hb
      simp [markedRawRootBadBoundary,hb,hgood]
  · simp [markedRawRootBadBoundary,markedRawBoundary,hz]

theorem markedRawRootBadBoundary_eq_sub_good
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x r d₀ Y : ℝ) {B : ℕ} {Z : Finset (ℤ × ℤ)}
    (w : Z → ℤ × ℤ) (z₀ : Z) (hz₀ : z₀.1 = (1,0)) (hw : w z₀ = (0,1))
    (s : MarkedRawState (markedRawActualPrimeBand e x) (markedPadSlots x) B Z) :
    markedRawRootBadBoundary e x d₀ Y z₀ (r:AddCircle (1:ℝ)) s =
      markedRawBoundary z₀ s -
        (if MarkedRawDirtyGood e x r d₀ Y w s then markedRawBoundary z₀ s else 0) := by
  rw [markedRawRootBadBoundary_eq_actual_bad e x r d₀ Y w z₀ hz₀ hw]
  split_ifs <;> simp

end
end ArtinMatthews
