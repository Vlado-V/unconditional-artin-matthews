module

public import ArtinMatthews.MarkedMinorArcDirtyCrudeRow
public import ArtinMatthews.MarkedMinorArcDirtyRowFreshMass
public import ArtinMatthews.MarkedMinorArcBanRawCollision


set_option backward.privateInPublic true
@[expose] public section

/-! Raw delta determinant branch only: actual fresh tilted expectation of
the literal dirty choice count. The distinct major comparison branch is
not covered by the raw determinant equation used here. -/
noncomputable section
namespace ArtinMatthews

open Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

private theorem dirty_split_sum {Ω : Type*} [Fintype Ω] (μ f : Ω → ℝ) (E : Ω → Prop)
    (hμ : ∀ t, 0 ≤ μ t) {g h : ℝ} (hg : 0 ≤ g)
    (hgood : ∀ t, ¬E t → f t ≤ g) (hcrude : ∀ t, f t ≤ h) :
    (∑ t, μ t*f t) ≤ (∑ t, μ t)*g+markedEventMass μ E*h := by
  classical
  calc
    _ ≤ ∑ t, (μ t*g+((if E t then (1:ℝ) else 0)*μ t)*h) := by
      apply Finset.sum_le_sum
      intro t _
      by_cases ht : E t
      · simp only [ht,ite_true,one_mul]
        exact (mul_le_mul_of_nonneg_left (hcrude t) (hμ t)).trans
          (le_add_of_nonneg_left (mul_nonneg (hμ t) hg))
      · simp only [ht,ite_false,zero_mul,zero_mul,add_zero]
        exact mul_le_mul_of_nonneg_left (hgood t ht) (hμ t)
    _ = _ := by rw [Finset.sum_add_distrib,← Finset.sum_mul,← Finset.sum_mul]; rfl

/-- Literal raw-delta choice expectation. Both the good-draw count and the
exceptional-draw count are proved from the actual finite choices. -/
theorem markedRawDirty_delta_choice_expectation_eventually
    {J R : Type*} [Fintype J] [DecidableEq J] [Fintype R] [DecidableEq R]
    (e : J → ℝ) (hinj : Function.Injective e)
    (eFresh : R → ℝ) (heFresh : ∀ j, (1/10:ℝ) ≤ eFresh j) :
    ∀ᶠ x : ℝ in atTop, ∀ (M B : ℕ)
      (source : MarkedRawActive (markedRawActualPrimeBand e x) M)
      (memory : MarkedRawMemory (markedRawActualPrimeBand e x) B) (jstar : J) (I : Finset J)
      (V : Finset (ℤ × ℤ)) (hV : ∀ v ∈ V, IsCoprime v.1 v.2) (z w : ℤ × ℤ)
      (Q : Finset ℤ) (r q ρ : ℝ) (newHits : (J → Fin M) → V → I → ℕ),
      0 < M → (∀ j, Function.Injective (source j)) →
      markedMinorIntegerDet z w=1 → markedMinorIntegerTau r z ≠ 0 →
      (∀ v ∈ V, |markedMinorIntegerTau r v/markedMinorIntegerTau r z| ≤ 16) →
      0 ≤ q → q ≤ 1 → 0 ≤ ρ → ρ < 1 →
      ((markedMinorIntegerTau r w/markedMinorIntegerTau r z:ℝ):AddCircle (1:ℝ)) ∉
        {s | Real.exp (-((Real.log x)^(e jstar))/4) ≤
          markedPairFailureProbability Q (markedFreshIntegerProduct eFresh x) (markedFreshHarmonicLaw eFresh x)
            (100*Real.exp (-((Real.log x)^(e jstar)))) s} →
      (∑ t : MarkedFreshPrimeTuple eFresh x, markedFreshTiltedLaw eFresh q x t *
        markedRawDirtyGoodChoiceMass source memory jstar I V hV z (markedFreshIntegerProduct eFresh x t)
          Q ρ newHits) ≤
        33*(1/(1-ρ)^2)^(I.card)*(2:ℝ)^(Fintype.card R)*
          ((B:ℝ)*(M:ℝ)⁻¹^(Fintype.card J)+(B:ℝ)^(I.card+1)*Real.exp (-((Real.log x)^(e jstar))/4)) := by
  classical
  have hfail : ∀ᶠ x : ℝ in atTop, ∀ j : J, ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      ∀ Q : Finset ℤ, ∀ s : AddCircle (1:ℝ),
      s ∉ {s | Real.exp (-((Real.log x)^(e j))/4) ≤
        markedPairFailureProbability Q (markedFreshIntegerProduct eFresh x) (markedFreshHarmonicLaw eFresh x)
          (100*Real.exp (-((Real.log x)^(e j)))) s} →
      markedPairFailureProbability Q (markedFreshIntegerProduct eFresh x) (markedFreshTiltedLaw eFresh q x)
        (100*Real.exp (-((Real.log x)^(e j)))) s <
          (2:ℝ)^(Fintype.card R)*Real.exp (-((Real.log x)^(e j))/4) :=
    eventually_all.mpr (fun j => marked_actual_fresh_failure_off_good_eventually eFresh heFresh (e j))
  filter_upwards [markedBan_actual_typed_disjoint_eventually e hinj,
    markedFreshTiltedLaw_mass_eventually eFresh heFresh,hfail] with x hdis hmass hfail
  intro M B source memory jstar I V hV z w Q r q ρ newHits hM hdist hd hz hbox hq0 hq1 hρ0 hρ1 hroot
  let S : AddCircle (1:ℝ) := (markedMinorIntegerTau r w/markedMinorIntegerTau r z:ℝ)
  let E (t : MarkedFreshPrimeTuple eFresh x) : Prop :=
    S ∈ markedPairBadRoots Q (markedFreshIntegerProduct eFresh x t) (100*Real.exp (-((Real.log x)^(e jstar))))
  let μ := markedFreshTiltedLaw eFresh q x
  let f (t : MarkedFreshPrimeTuple eFresh x) := markedRawDirtyGoodChoiceMass source memory jstar I V hV z
    (markedFreshIntegerProduct eFresh x t) Q ρ newHits
  let g : ℝ := 33*(B:ℝ)*(M:ℝ)⁻¹^(Fintype.card J)*(1/(1-ρ)^2)^(I.card)
  let h : ℝ := 33*(B:ℝ)^(I.card+1)*(1/(1-ρ)^2)^(I.card)
  have hμ := hmass q hq0 hq1
  have hgood (t) (ht : ¬E t) : f t ≤ g := by
    apply markedRawDirtyGoodChoiceMass_le source hdis hdist memory jstar I V hV z w
      (markedFreshIntegerProduct eFresh x t) Q r hd hz hbox (Real.exp_pos _) hρ0 hρ1 ?_ ht newHits
    intro k _
    have hp : ((memory.2 jstar k).1.1:ℕ) ∈ markedLogPowerBand (e jstar) x :=
      (mem_markedRawPrimeBand _ _).mp (memory.2 jstar k).1.2
    calc
      _ ≤ 1/Real.exp ((Real.log x)^(e jstar)) :=
        one_div_le_one_div_of_le (Real.exp_pos _) (mem_markedLogPowerBand.mp hp).2.1
      _ = _ := by rw [one_div,Real.exp_neg]
  have hcrude (t) : f t ≤ h := markedRawDirtyGoodChoiceMass_crude_le hM source memory jstar I V hV z w
    (markedFreshIntegerProduct eFresh x t) Q r hd hz hbox hρ0 hρ1 newHits
  have hex : markedEventMass μ E ≤ (2:ℝ)^(Fintype.card R)*Real.exp (-((Real.log x)^(e jstar))/4) := by
    rw [← markedPairFailureProbability_eq_eventMass]
    exact (hfail jstar q hq0 hq1 Q S hroot).le
  apply (dirty_split_sum μ f E hμ.1 (by dsimp [g]; positivity) hgood hcrude).trans
  calc
    _ ≤ (2:ℝ)^(Fintype.card R)*g+
        ((2:ℝ)^(Fintype.card R)*Real.exp (-((Real.log x)^(e jstar))/4))*h :=
      add_le_add (mul_le_mul_of_nonneg_right hμ.2 (by dsimp [g]; positivity))
        (mul_le_mul_of_nonneg_right hex (by dsimp [h]; positivity))
    _ = _ := by dsimp [g,h]; ring

end ArtinMatthews
