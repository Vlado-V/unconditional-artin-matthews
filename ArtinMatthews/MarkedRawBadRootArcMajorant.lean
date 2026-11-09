module

public import ArtinMatthews.MarkedRootArcMajorant


set_option backward.privateInPublic true
@[expose] public section

/-! The actual first-plus-second bad-root indicator has a positive finite
elementary-arc majorant. The true fresh harmonic weights and threshold
division remain visible for the weighted root-counting theorem. -/
namespace ArtinMatthews
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def markedRawFirstRootArcMajorant {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {M : ℕ} (a : MarkedRawActive P M) (d₀ Y : ℝ)
    (θ : AddCircle (1:ℝ)) : ℝ :=
  ∑ p : (markedRawDyadicOmissions a d₀) × ↥(Finset.Icc 1 ⌊Y^(1/5:ℝ)⌋₊),
    if θ ∈ markedFirstRootArcSet
      (fun choice : markedRawDyadicOmissions a d₀ =>
        markedSourceCopiedProduct (markedRawNumericActive a) choice.1)
      ⌊Y^(1/5:ℝ)⌋₊ (Y^(-7/10:ℝ)) p then 1 else 0

def markedRawBetaRootArcMajorant {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x : ℝ)
    (a : MarkedRawActive (markedRawActualPrimeBand e x) (markedPadSlots x))
    (θ : AddCircle (1:ℝ)) : ℝ :=
  ∑ p : Finset J × J,
    if p.2 ∈ p.1 ∧ (∀ j ∈ p.1,e j ≤ e p.2) then
      (∑ t : MarkedFreshPrimeTuple (fun j : ↥(Finset.univ \ p.1) => e j.1) x,
        markedFreshHarmonicLaw (fun j : ↥(Finset.univ \ p.1) => e j.1) x t *
          markedPairRootArcMajorant (markedRawDirtyFullTrials e x a (p.1.erase p.2))
            (markedFreshIntegerProduct (fun j : ↥(Finset.univ \ p.1) => e j.1) x t)
            (100*Real.exp (-((Real.log x)^(e p.2)))) θ) /
        Real.exp (-((Real.log x)^(e p.2))/4)
    else 0

def markedRawBadRootArcMajorant {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x d₀ Y : ℝ)
    (a : MarkedRawActive (markedRawActualPrimeBand e x) (markedPadSlots x))
    (θ : AddCircle (1:ℝ)) : ℝ :=
  markedRawFirstRootArcMajorant a d₀ Y θ + markedRawBetaRootArcMajorant e x a θ

theorem markedRawFirstBadRoot_indicator_le_arcs
    {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {M : ℕ} (a : MarkedRawActive P M) (d₀ Y : ℝ)
    (θ : AddCircle (1:ℝ)) :
    (if θ ∈ markedRawFirstBadRootSet a d₀ Y then (1:ℝ) else 0) ≤
      markedRawFirstRootArcMajorant a d₀ Y θ :=
  markedFirstBadRoots_indicator_le_arcs _ _ _ θ

theorem markedRawBetaBadRoot_indicator_le_arcs
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x : ℝ)
    (hμ : ∀ I : Finset J,∀ t : MarkedFreshPrimeTuple (fun j : ↥(Finset.univ \ I) => e j.1) x,
      0 ≤ markedFreshHarmonicLaw (fun j : ↥(Finset.univ \ I) => e j.1) x t)
    (a : MarkedRawActive (markedRawActualPrimeBand e x) (markedPadSlots x))
    (θ : AddCircle (1:ℝ)) :
    (if θ ∈ markedRawDirtyBetaBadRoots e x a then (1:ℝ) else 0) ≤
      markedRawBetaRootArcMajorant e x a θ := by
  have h := markedFiniteUnion_indicator_le
    (fun p : Finset J × J => if p.2 ∈ p.1 ∧ (∀ j ∈ p.1,e j ≤ e p.2) then
      markedRawDirtyBetaEvent e x a p.1 p.2 else ∅) θ
  apply h.trans
  unfold markedRawBetaRootArcMajorant
  apply Finset.sum_le_sum
  intro p _
  by_cases hp : p.2 ∈ p.1 ∧ (∀ j ∈ p.1,e j ≤ e p.2)
  · simp only [ite_eq_left hp]
    exact markedPairThreshold_indicator_le_arcs _ _ _ (hμ p.1) _ (Real.exp_pos _) θ
  · simp [hp]

theorem markedRawBadRoot_indicator_le_arcs
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x d₀ Y : ℝ)
    (hμ : ∀ I : Finset J,∀ t : MarkedFreshPrimeTuple (fun j : ↥(Finset.univ \ I) => e j.1) x,
      0 ≤ markedFreshHarmonicLaw (fun j : ↥(Finset.univ \ I) => e j.1) x t)
    (a : MarkedRawActive (markedRawActualPrimeBand e x) (markedPadSlots x))
    (θ : AddCircle (1:ℝ)) :
    (if θ ∈ markedRawBadRootSet e x d₀ Y a then (1:ℝ) else 0) ≤
      markedRawBadRootArcMajorant e x d₀ Y a θ := by
  have hfirst := markedRawFirstBadRoot_indicator_le_arcs a d₀ Y θ
  have hsecond := markedRawBetaBadRoot_indicator_le_arcs e x hμ a θ
  have hu : (if θ ∈ markedRawBadRootSet e x d₀ Y a then (1:ℝ) else 0) ≤
      (if θ ∈ markedRawFirstBadRootSet a d₀ Y then (1:ℝ) else 0) +
        (if θ ∈ markedRawDirtyBetaBadRoots e x a then (1:ℝ) else 0) := by
    by_cases h₁ : θ ∈ markedRawFirstBadRootSet a d₀ Y <;>
      by_cases h₂ : θ ∈ markedRawDirtyBetaBadRoots e x a <;> simp [markedRawBadRootSet,h₁,h₂]
  exact hu.trans (add_le_add hfirst hsecond)

theorem markedRawBadRoot_indicator_le_arcs_eventually
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j) :
    ∀ᶠ x : ℝ in atTop,∀ (d₀ Y : ℝ)
      (a : MarkedRawActive (markedRawActualPrimeBand e x) (markedPadSlots x))
      (θ : AddCircle (1:ℝ)),
      (if θ ∈ markedRawBadRootSet e x d₀ Y a then (1:ℝ) else 0) ≤
        markedRawBadRootArcMajorant e x d₀ Y a θ := by
  have h := eventually_all.mpr (fun I : Finset J =>
    marked_actual_harmonic_fresh_probability_eventually (fun j : ↥(Finset.univ \ I) => e j.1)
      (fun j => by linarith [he j.1]))
  filter_upwards [h] with x hx
  intro d₀ Y a θ
  exact markedRawBadRoot_indicator_le_arcs e x d₀ Y (fun I => (hx I).1) a θ

end
end ArtinMatthews
