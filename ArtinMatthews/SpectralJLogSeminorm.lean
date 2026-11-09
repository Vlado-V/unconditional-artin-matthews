module

public import ArtinMatthews.SpectralJLogConjugation


set_option backward.privateInPublic true
@[expose] public section

/-! The actual compact logarithmic family has uniform physical Sturm
seminorms. No seminorm bound is supplied as a hypothesis. -/
namespace ArtinMatthews
open Set MeasureTheory
open SourceSturm
open scoped ContDiff
noncomputable section

theorem spectralJLogProfile_sturmL1_bound {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g)
    {a α β M : ℝ} (ha : 0 < a) (hs : tsupport g ⊆ Icc α β)
    (hM : 0 ≤ M) (hb : ∀ v ∈ Icc α β, ‖g v‖ ≤ M) :
    sturmL1 (spectralJLogProfile g a) ≤ M*Real.exp (β-α) := by
  let f := spectralJLogProfile g a
  let lo := a*Real.exp α
  let hi := a*Real.exp β
  have hlo : 0 < lo := mul_pos ha (Real.exp_pos _)
  have hhi : 0 < hi := mul_pos ha (Real.exp_pos _)
  have hfs : tsupport f ⊆ Icc lo hi := spectralJLogProfile_tsupport ha hs
  have hfp : tsupport f ⊆ Ioi 0 := spectralJLogProfile_positive_tsupport ha hs
  have hz (x : ℝ) (hx : x ∉ Icc lo hi) : ‖f x‖/x = 0 := by
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hfs h)), norm_zero, zero_div]
  have hIoi : (∫ x in Ioi (0 : ℝ), ‖f x‖/x) = ∫ x, ‖f x‖/x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => by
        rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hfp h)), norm_zero, zero_div])
  have hIcc : (∫ x in Icc lo hi, ‖f x‖/x) = ∫ x, ‖f x‖/x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hz
  have hnonneg : 0 ≤ ∫ x in Icc lo hi, ‖f x‖/x := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact div_nonneg (norm_nonneg _) (hlo.le.trans hx.1)
  have hpoint (x : ℝ) (hx : x ∈ Icc lo hi) : ‖‖f x‖/x‖ ≤ M/lo := by
    have hx0 : 0 < x := hlo.trans_le hx.1
    have hf : ‖f x‖ ≤ M := by
      by_cases hmem : Real.log (x/a) ∈ Icc α β
      · change ‖spectralJLogProfile g a x‖ ≤ M
        rw [spectralJLogProfile, if_pos hx0]
        exact hb _ hmem
      · have hg0 : g (Real.log (x/a)) = 0 :=
          image_eq_zero_of_notMem_tsupport (fun h => hmem (hs h))
        simp only [f, spectralJLogProfile, if_pos hx0, hg0, norm_zero]
        exact hM
    rw [Real.norm_of_nonneg (div_nonneg (norm_nonneg _) hx0.le)]
    exact (div_le_div_of_nonneg_right hf hx0.le).trans
      (div_le_div_of_nonneg_left hM hlo hx.1)
  change (∫ x in Ioi (0 : ℝ), ‖f x‖/x) ≤ _
  rw [hIoi, ← hIcc, ← Real.norm_of_nonneg hnonneg]
  calc
    _ ≤ (M/lo)*volume.real (Icc lo hi) :=
      norm_setIntegral_le_of_norm_le_const measure_Icc_lt_top hpoint
    _ ≤ (M/lo)*hi := by
      apply mul_le_mul_of_nonneg_left _ (div_nonneg hM hlo.le)
      rw [Real.volume_real_Icc]
      exact max_le (by linarith) hhi.le
    _ = _ := by
      dsimp [lo,hi]
      rw [Real.exp_sub]
      field_simp [ha.ne',(Real.exp_pos α).ne'] <;> ring

def spectralJOscillatoryLogProfile (A : ℝ → ℂ) (B : ℝ → ℝ) (a u : ℝ) : ℝ → ℂ :=
  spectralJLogProfile (markedOscillatoryFamily A B u) a

theorem spectralJOscillatoryFamily_tsupport (A : ℝ → ℂ) (B : ℝ → ℝ) (u : ℝ) :
    tsupport (markedOscillatoryFamily A B u) ⊆ tsupport A := by
  change tsupport (A * markedOscillatoryPhase B u) ⊆ tsupport A
  exact tsupport_mul_subset_left

theorem spectralJOscillatoryLogProfile_smooth
    (A : ℝ → ℂ) (B : ℝ → ℝ) (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B)
    {α β a : ℝ} (hs : tsupport A ⊆ Icc α β) (ha : 0 < a) (u : ℝ) :
    ContDiff ℝ ∞ (spectralJOscillatoryLogProfile A B a u) :=
  spectralJLogProfile_contDiff (markedOscillatoryFamily_contDiff A B hA hB u) ha
    ((spectralJOscillatoryFamily_tsupport A B u).trans hs)

theorem spectralJOscillatoryLogProfile_sturmL1
    (A : ℝ → ℂ) (B : ℝ → ℝ) (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B)
    {α β : ℝ} (hs : tsupport A ⊆ Icc α β) (R : ℝ) (hR : 0 ≤ R) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ a u : ℝ, 0 < a → a ≤ R →
      sturmL1 ((sturmD^[n]) (spectralJOscillatoryLogProfile A B a u)) ≤
        C*(1+|u|)^(2*n) := by
  obtain ⟨C,hC,hb⟩ := spectralJLogSturm_iterate_bound A B hA hB (Icc α β) isCompact_Icc R hR n 0
  refine ⟨C*Real.exp (β-α), mul_pos hC (Real.exp_pos _), ?_⟩
  intro a u ha haR
  let g := ((spectralJLogSturm a)^[n]) (markedOscillatoryFamily A B u)
  have hg : ContDiff ℝ ∞ g :=
    spectralJLogSturm_iterate_smooth a n (markedOscillatoryFamily_contDiff A B hA hB u)
  have hgs : tsupport g ⊆ Icc α β :=
    (spectralJLogSturm_iterate_tsupport a n _).trans
      ((spectralJOscillatoryFamily_tsupport A B u).trans hs)
  have hgb (v : ℝ) (hv : v ∈ Icc α β) : ‖g v‖ ≤ C*(1+|u|)^(2*n) := by
    simpa only [Nat.zero_add, iteratedDeriv_zero] using hb a u v (by rwa [abs_of_pos ha]) hv
  change sturmL1 ((sturmD^[n]) (spectralJLogProfile (markedOscillatoryFamily A B u) a)) ≤ _
  rw [spectralJLogProfile_sturm_iterate n (markedOscillatoryFamily_contDiff A B hA hB u)
    ha ((spectralJOscillatoryFamily_tsupport A B u).trans hs)]
  exact (spectralJLogProfile_sturmL1_bound hg ha hgs (by positivity) hgb).trans_eq (by ring)

end
end ArtinMatthews
