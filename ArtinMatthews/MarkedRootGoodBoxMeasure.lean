module

public import ArtinMatthews.MarkedRootGoodBoxCells
public import ArtinMatthews.MarkedRawGoodRootMeasure


set_option backward.privateInPublic true
@[expose] public section

/-! Measurability of the actual finite first/beta test and its transported
moving-box observable, including poles with Lean's literal division. -/

noncomputable section
namespace ArtinMatthews
open MeasureTheory
attribute [local instance] Classical.propDecidable

theorem markedRawCircleGood_measurable {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x : ℝ) {M : ℕ}
    (a : MarkedRawActive (markedRawActualPrimeBand e x) M) (d₀ Y : ℝ) :
    MeasurableSet {θ : AddCircle (1:ℝ) | MarkedRawCircleGood e x a d₀ Y θ} := by
  change MeasurableSet ((markedRawFirstBadRootSet a d₀ Y)ᶜ ∩ {θ | ∀ (I : Finset J) (j : J),
    j ∈ I → (∀ k ∈ I,e k ≤ e j) →
    ¬Real.exp (-((Real.log x)^(e j))/4) ≤
      markedPairFailureProbability (markedRawDirtyFullTrials e x a (I.erase j))
        (markedFreshIntegerProduct (fun k : ↥(Finset.univ \ I) => e k.1) x)
        (markedFreshHarmonicLaw (fun k : ↥(Finset.univ \ I) => e k.1) x)
        (100*Real.exp (-((Real.log x)^(e j)))) θ})
  apply (markedRawFirstBadRootSet_measurable a d₀ Y).compl.inter
  simp only [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro I
  apply MeasurableSet.iInter
  intro j
  apply MeasurableSet.iInter
  intro _
  apply MeasurableSet.iInter
  intro _
  exact (measurableSet_le measurable_const (markedPairFailureProbability_measurable _ _ _ _)).compl

theorem markedRootPhysicalGoodBox_measurable {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x : ℝ) {M : ℕ}
    (a : MarkedRawActive (markedRawActualPrimeBand e x) M) (d₀ Y U V : ℝ)
    (z w : Fin 2 → ℝ) :
    MeasurableSet {p | MarkedRootPhysicalGoodBox e x a d₀ Y U V z w p} := by
  have hf : Measurable (markedRootBoxFirst z) := by unfold markedRootBoxFirst markedTau; fun_prop
  have hg : Measurable (markedRootBoxSecond U V z) := by unfold markedRootBoxSecond markedTau; fun_prop
  have hr : Measurable (fun p : ℝ × (ℝ × ℝ) => markedTransportedRatio p.1 z w) := by
    unfold markedTransportedRatio markedTau
    fun_prop
  have hc := (AddCircle.continuous_mk' (1:ℝ)).measurable.comp hr
  exact ((measurableSet_Icc.preimage hf).inter (measurableSet_Icc.preimage hg)).inter
    ((markedRawCircleGood_measurable e x a d₀ Y).preimage hc)

end ArtinMatthews
