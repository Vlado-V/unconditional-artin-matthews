module

public import ArtinMatthews.MarkedMinorArcDirtySecondGood


set_option backward.privateInPublic true
@[expose] public section

/-! The combined good event underlying the actual two-sided endpoint
projection, retained explicitly for good/error decompositions. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.propDecidable

def MarkedRawDirtyGood {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x r d₀ Y : ℝ) {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (w : Z → ℤ × ℤ) (s : MarkedRawState (markedRawActualPrimeBand e x) M B Z) : Prop :=
  MarkedRawFirstGood r d₀ Y w s ∧ MarkedRawDirtySecondGood e x r w s

theorem markedRawDirtyGoodCutoff_eq_ite {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x r d₀ Y : ℝ) {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (w : Z → ℤ × ℤ) (χ : MarkedRawState (markedRawActualPrimeBand e x) M B Z → ℂ)
    (s : MarkedRawState (markedRawActualPrimeBand e x) M B Z) :
    markedRawDirtyGoodCutoff e x r d₀ Y w χ s=
      if MarkedRawDirtyGood e x r d₀ Y w s then χ s else 0 := by
  unfold markedRawDirtyGoodCutoff markedRawFirstGoodCutoff markedRawDirtySecondGoodCutoff MarkedRawDirtyGood
  split_ifs <;> simp_all

theorem markedRawDirtyGood_pending_permute {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x r d₀ Y : ℝ) {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (w : Z → ℤ × ℤ) (z : Z) (a : MarkedRawActive (markedRawActualPrimeBand e x) M)
    (m : MarkedRawMemory (markedRawActualPrimeBand e x) B)
    (σ : (j : J) → Equiv.Perm (Fin (m.1.1 j:ℕ))) :
    MarkedRawDirtyGood e x r d₀ Y w (z,(a,markedRawMemoryPermute m σ)) ↔
      MarkedRawDirtyGood e x r d₀ Y w (z,(a,m)) := Iff.rfl

end
end ArtinMatthews
