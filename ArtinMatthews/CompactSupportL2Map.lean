module

public import Mathlib


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open MeasureTheory Set
noncomputable section

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (S : Set X) [CompactSpace S]

def compactContinuousZeroExtension (f : C(S, ℂ)) : X → ℂ :=
  Function.extend (Subtype.val : S → X) f 0

theorem compactContinuousZeroExtension_mem (f : C(S, ℂ)) (x : X) (hx : x ∈ S) :
    compactContinuousZeroExtension S f x = f ⟨x,hx⟩ :=
  Subtype.val_injective.extend_apply f 0 ⟨x,hx⟩

theorem compactContinuousZeroExtension_notMem (f : C(S, ℂ)) (x : X) (hx : x ∉ S) :
    compactContinuousZeroExtension S f x = 0 := by
  apply Function.extend_apply'
  rintro ⟨y,hy⟩
  exact hx (hy ▸ y.property)

theorem compactContinuousZeroExtension_measurable (hs : MeasurableSet S) (f : C(S, ℂ)) :
    Measurable (compactContinuousZeroExtension S f) :=
  (MeasurableEmbedding.subtype_coe hs).measurable_extend f.continuous.measurable measurable_const

theorem compactContinuousZeroExtension_norm_bound (f : C(S, ℂ)) (x : X) :
    ‖compactContinuousZeroExtension S f x‖ ≤ ‖S.indicator (fun _ : X => ‖f‖) x‖ := by
  classical
  by_cases hx : x ∈ S
  · rw [compactContinuousZeroExtension_mem S f x hx,indicator_of_mem hx]
    simpa only [Real.norm_eq_abs,abs_norm] using f.norm_coe_le_norm ⟨x,hx⟩
  · simp [compactContinuousZeroExtension_notMem S f x hx,indicator_of_notMem hx]

theorem compactContinuousZeroExtension_memLp (hs : MeasurableSet S)
    (μ : Measure X) (hμS : μ S ≠ ⊤) (f : C(S, ℂ)) :
    MemLp (compactContinuousZeroExtension S f) 2 μ :=
  (memLp_indicator_const 2 hs.nullMeasurableSet ‖f‖ (Or.inr hμS)).mono
    (compactContinuousZeroExtension_measurable S hs f).aestronglyMeasurable
    (Filter.Eventually.of_forall (compactContinuousZeroExtension_norm_bound S f))

def compactContinuousToL2 (hs : MeasurableSet S) (μ : Measure X) (hμS : μ S ≠ ⊤)
    (f : C(S, ℂ)) : Lp ℂ 2 μ :=
  (compactContinuousZeroExtension_memLp S hs μ hμS f).toLp (compactContinuousZeroExtension S f)

theorem compactContinuousToL2_coe (hs : MeasurableSet S) (μ : Measure X) (hμS : μ S ≠ ⊤)
    (f : C(S, ℂ)) : compactContinuousToL2 S hs μ hμS f =ᵐ[μ] compactContinuousZeroExtension S f :=
  MemLp.coeFn_toLp _

theorem compactContinuousToL2_add (hs : MeasurableSet S) (μ : Measure X) (hμS : μ S ≠ ⊤)
    (f g : C(S, ℂ)) : compactContinuousToL2 S hs μ hμS (f+g) =
      compactContinuousToL2 S hs μ hμS f + compactContinuousToL2 S hs μ hμS g := by
  apply Lp.ext
  filter_upwards [compactContinuousToL2_coe S hs μ hμS (f+g),
    compactContinuousToL2_coe S hs μ hμS f,compactContinuousToL2_coe S hs μ hμS g,
    Lp.coeFn_add (compactContinuousToL2 S hs μ hμS f) (compactContinuousToL2 S hs μ hμS g)] with x hfg hf hg hsum
  simp only [Pi.add_apply] at hsum
  rw [hfg,hsum,hf,hg]
  by_cases hx : x ∈ S
  · simp only [compactContinuousZeroExtension_mem S _ x hx,ContinuousMap.add_apply]
  · simp only [compactContinuousZeroExtension_notMem S _ x hx,add_zero]

theorem compactContinuousToL2_smul (hs : MeasurableSet S) (μ : Measure X) (hμS : μ S ≠ ⊤)
    (c : ℂ) (f : C(S, ℂ)) : compactContinuousToL2 S hs μ hμS (c • f) =
      c • compactContinuousToL2 S hs μ hμS f := by
  apply Lp.ext
  filter_upwards [compactContinuousToL2_coe S hs μ hμS (c • f),
    compactContinuousToL2_coe S hs μ hμS f,Lp.coeFn_smul c (compactContinuousToL2 S hs μ hμS f)] with x hcf hf hsmul
  simp only [Pi.smul_apply] at hsmul
  rw [hcf,hsmul,hf]
  by_cases hx : x ∈ S
  · simp only [compactContinuousZeroExtension_mem S _ x hx,ContinuousMap.smul_apply]
  · simp only [compactContinuousZeroExtension_notMem S _ x hx,smul_zero]

theorem compactContinuousToL2_norm (hs : MeasurableSet S) (μ : Measure X) (hμS : μ S ≠ ⊤)
    (f : C(S, ℂ)) : ‖compactContinuousToL2 S hs μ hμS f‖ ≤
      μ.real S ^ (1 / (2 : ℝ)) * ‖f‖ := by
  have hcomp : ‖compactContinuousToL2 S hs μ hμS f‖ ≤
      ‖indicatorConstLp 2 hs hμS ‖f‖‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [compactContinuousToL2_coe S hs μ hμS f,
      indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμS) (c := ‖f‖)] with x hf hi
    rw [hf,hi]
    exact compactContinuousZeroExtension_norm_bound S f x
  apply hcomp.trans
  simpa [mul_comm] using
    (norm_indicatorConstLp_le (p := 2) (hs := hs) (hμs := hμS) (c := ‖f‖))

def compactContinuousToL2L (hs : MeasurableSet S) (μ : Measure X) (hμS : μ S ≠ ⊤) :
    C(S, ℂ) →L[ℂ] Lp ℂ 2 μ :=
  LinearMap.mkContinuous
    { toFun := compactContinuousToL2 S hs μ hμS
      map_add' := compactContinuousToL2_add S hs μ hμS
      map_smul' := compactContinuousToL2_smul S hs μ hμS }
    (μ.real S ^ (1 / (2 : ℝ))) (compactContinuousToL2_norm S hs μ hμS)

end
end ArtinMatthews
