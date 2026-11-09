module

public import ArtinMatthews.GiantCandidateSignedCorrelationDecay
public import ArtinMatthews.GiantCandidateDyadExtraction
public import ArtinMatthews.MarkedEstimateSieveParameters


set_option backward.privateInPublic true
@[expose] public section

/-! The analytic input is the original normalized shifted correlation
on each retained family. The signed expansion and failed mass then
give the ordinary tuple estimate at the same cutoff. -/

noncomputable section
namespace ArtinMatthews

open Filter Set
open scoped Asymptotics ContDiff

def GiantCandidateRetainedCorrelationLogSaving {J : Type*} [Fintype J]
    (e : J → ℝ) {M : ℕ} (χ : DirichletCharacter ℂ M)
    (ε : ℝ) (Φ : ℝ → ℝ) (T γ q : ℝ) (j : ℕ) (threshold : ℝ) : Prop :=
  ∀ A : ℝ, ∀ᶠ x : ℝ in atTop, ∀ S ∈ giantCandidateRetainedOutcomes x threshold,
    ‖giantCandidateActualUnguardedShiftedCorrelation (giantCandidateFullPrimes x)
      (fun i : ↥S => giantCandidateGroup x i.val) e χ ε Φ T γ q j x‖ ≤ (Real.log x)^(-A)

def GiantOrdinaryRetainedCorrelationInput (ε : ℝ) (Φ : ℝ → ℝ) (q : ℝ) : Prop :=
  ∀ T : ℝ, 1 < T → T < 2 → Function.support Φ ⊆ Ioo 1 T →
    ∀ (M : ℕ) [NeZero M], ∀ m ≥ 20000,
      let γ := markedSieveExponent (ε/4) m
      ∀ j ∈ Finset.Icc 2 ⌈2/γ⌉₊, ∀ threshold : ℝ, 0 < threshold →
      ∀ χ : DirichletCharacter ℂ M, ∃ K₀ : ℕ, ∀ K ≥ K₀, ∀ e : Fin K → ℝ,
        (∀ i, (1/10 : ℝ) < e i ∧ e i < 1/5) → Function.Injective e →
        GiantCandidateRetainedCorrelationLogSaving e χ ε Φ T γ q j threshold

theorem giant_ordinary_tuple_isLittleO_of_retained_correlation {J : Type}
    [Fintype J] [DecidableEq J] (e : J → ℝ) (hinj : Function.Injective e)
    (he : ∀ i, (1/10 : ℝ) < e i ∧ e i < 1/5)
    {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M)
    (Φ : ℝ → ℝ) {a T : ℝ} (ha : 0 < a) (hT : 0 < T)
    (hsupp : Function.support Φ ⊆ Icc a T) (hΦ : ContDiff ℝ ∞ Φ)
    {γ q threshold : ℝ} (hγ : 0 < γ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    {ε : ℝ} (hε : 0 < ε) (hεq : ε < 1/4) (j : ℕ) (hj : 2 ≤ j)
    (hdepth : 100*(5*(29+2*(((j-1)*(j-1)+6 : ℕ) : ℝ))+36) < (Fintype.card J : ℝ))
    (hmean : GiantCandidateUniformFailedBoxDecay γ q threshold j)
    (hcorr : GiantCandidateRetainedCorrelationLogSaving e χ ε Φ T γ q j threshold) :
    giantOrdinaryTupleSum e χ (giantMarkedCenteredCore ε) Φ (T+1) γ j
      =o[atTop] (fun x : ℝ => x/Real.log x) := by
  have hdiff := giant_ordinary_tuple_sub_signed_isLittleO_of_dyad_mean e hinj he χ Φ ha hT
    hsupp hΦ hγ hq0 hq1 hε hεq j hj hdepth hmean
  have hsum := giant_candidate_signedCorrelationSum_isLittleO_of_active e χ ε Φ T γ q j
    threshold hq0 hq1 (by omega) hcorr
  apply (hdiff.add hsum).congr' _ EventuallyEq.rfl
  exact Filter.Eventually.of_forall (fun _ => sub_add_cancel _ _)

end ArtinMatthews
