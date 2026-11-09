module

public import ArtinMatthews.GiantOrdinaryRetainedCorrelation
public import ArtinMatthews.GiantCandidateActualConcentration
public import ArtinMatthews.FullMainFixedCutoff
public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality


set_option backward.privateInPublic true
@[expose] public section

/-! Actual failed-box concentration chooses the retention threshold.
The finite maximum of the required marking depths is taken before the
array, as in the ordinary tuple mean. -/

noncomputable section
namespace ArtinMatthews

open Filter Set
open scoped Asymptotics ContDiff

theorem giantOrdinaryTupleCancellationInput_of_retained_correlation
    {ε q : ℝ} (hε : 0 < ε) (hεq : ε < 1/4) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ)
    (hsource : GiantOrdinaryRetainedCorrelationInput ε Φ q) :
    GiantOrdinaryTupleCancellationInput ε Φ := by
  classical
  intro T hT₁ hT₂ hs M instM m hm
  let γ := markedSieveExponent (ε/4) m
  let I := Finset.Icc 2 ⌈2/γ⌉₊
  have hγ : 0 < γ := markedSieveExponent_pos (by positivity) m
  have hactual (j : ↥I) : ∃ threshold : ℝ, 0 < threshold ∧
      GiantCandidateUniformFailedBoxDecay γ q threshold j.val := by
    have hj : 2 ≤ j.val := (Finset.mem_Icc.mp j.property).1
    exact giant_candidate_uniformFailedBoxDecay_actual hγ hq0 hq1 j.val (by omega)
  choose threshold hthreshold hfailed using hactual
  let Test := ↥I × DirichletCharacter ℂ M
  have hlocal (p : Test) : ∃ K₀ : ℕ, ∀ K ≥ K₀, ∀ e : Fin K → ℝ,
      (∀ i, (1/10 : ℝ) < e i ∧ e i < 1/5) → Function.Injective e →
      GiantCandidateRetainedCorrelationLogSaving e p.2 ε Φ T γ q p.1.val (threshold p.1) :=
    hsource T hT₁ hT₂ hs M m hm p.1.val p.1.property (threshold p.1) (hthreshold p.1) p.2
  choose k₀ hcorr using hlocal
  let depth (j : ℕ) : ℝ := 100*(5*(29+2*(((j-1)*(j-1)+6 : ℕ) : ℝ))+36)
  let required (p : Test) := max (k₀ p) (⌈depth p.1.val⌉₊+1)
  let K := (Finset.univ : Finset Test).sup required
  refine ⟨K,?_⟩
  intro e he hinj χ j hj
  let i : ↥I := ⟨j,hj⟩
  let p : Test := (i,χ)
  have hK : required p ≤ K := Finset.le_sup (Finset.mem_univ p)
  have hk₀ : k₀ p ≤ K := (le_max_left _ _).trans hK
  have hceilK : ⌈depth j⌉₊+1 ≤ K := (le_max_right _ _).trans hK
  have hdepth : depth j < (Fintype.card (Fin K) : ℝ) := by
    have hceil : (⌈depth j⌉₊ : ℝ) < ((⌈depth j⌉₊+1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.lt_succ_self ⌈depth j⌉₊
    simpa only [Fintype.card_fin] using
      (Nat.le_ceil (depth j)).trans_lt (hceil.trans_le (Nat.cast_le.mpr hceilK))
  exact giant_ordinary_tuple_isLittleO_of_retained_correlation e hinj he χ Φ
    zero_lt_one (zero_lt_one.trans hT₁) (hs.trans Ioo_subset_Icc_self) hΦ
    hγ hq0 hq1 hε hεq j (Finset.mem_Icc.mp hj).1 hdepth (hfailed i)
    (hcorr p K hk₀ e he hinj)

theorem giantMainOrdinaryTupleCancellationInput_of_retained_correlation
    (hsource : GiantOrdinaryRetainedCorrelationInput giantMainEpsilon giantMainSmoothCutoff (1/2)) :
    GiantOrdinaryTupleCancellationInput giantMainEpsilon giantMainSmoothCutoff :=
  giantOrdinaryTupleCancellationInput_of_retained_correlation giantMainEpsilon_bounds.1
    (giantMainEpsilon_bounds.2.trans (by norm_num)) (by norm_num) (by norm_num)
    giantMainSmoothCutoff giantMainSmoothCutoff_spec.1 hsource

end ArtinMatthews
