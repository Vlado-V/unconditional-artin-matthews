module

public import ArtinMatthews.SourceKPAdelicHeightProductChart
public import ArtinMatthews.SourceKPAdelicHeightFiniteBound
public import ArtinMatthews.SourceKPAdelicCuspBand
public import ArtinMatthews.SourceAdelicHeightFibers
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition


set_option backward.privateInPublic true
@[expose] public section

/-! The orbit-height transition in the actual product upper chart. -/

namespace ArtinMatthews

open NumberField Matrix OAI.CubicEisenstein SourceArchJacquet Filter
open scoped NumberField MatrixGroups AdeleRing Topology ContDiff Classical

noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPAdelicScalarCutoff (T : ℝ) (q : SourceKPAdelicProjective K hζ) : ℝ :=
  Real.smoothTransition (Real.log (sourceKPAdelicOrbitHeight K hζ q) - Real.log T)

def sourceKPAdelicScalarCutoffProduct (T : ℝ) (q : SourceKPAdelicProjective K hζ)
    (p : InfinitePlace K → EuclideanSpatial) : ℝ :=
  if hp : ∀ v, 0 < p v 2 then sourceKPAdelicScalarCutoff K hζ T
    (q * (ProjGenLinGroup.mk (sourceArchUpperHalfspaceMatrix K hζ p hp), 1)) else 0

private theorem productHeight_rational_eq (q : SourceKPAdelicProjective K hζ)
    (γ : PGL(2,K)) (p : InfinitePlace K → EuclideanSpatial) (hp : ∀ v, 0 < p v 2) :
    sourceKPAdelicProductHeight K hζ (sourceKPAdelicProjectiveRationalLift K hζ γ * q) p =
      sourceKPAdelicCoverHeight K hζ (sourceKPAdelicProjectiveRationalLift K hζ γ *
        (q * (ProjGenLinGroup.mk (sourceArchUpperHalfspaceMatrix K hζ p hp), 1))) := by
  rw [sourceKPAdelicProductHeight, dif_pos hp, mul_assoc]

theorem sourceKPAdelicScalarCutoffProduct_eventuallyEq_of_high
    (T : ℝ) (q : SourceKPAdelicProjective K hζ) (γ : PGL(2,K))
    (p : InfinitePlace K → EuclideanSpatial) (hp : ∀ v, 0 < p v 2)
    (hhigh : 1 < sourceKPAdelicProductHeight K hζ (sourceKPAdelicProjectiveRationalLift K hζ γ * q) p) :
    sourceKPAdelicScalarCutoffProduct K hζ T q =ᶠ[𝓝 p] fun x =>
      Real.smoothTransition
        (Real.log (sourceKPAdelicProductHeight K hζ
          (sourceKPAdelicProjectiveRationalLift K hζ γ * q) x) - Real.log T) := by
  have hnear := (sourceKPAdelicProductHeight_contDiffAt K hζ
    (sourceKPAdelicProjectiveRationalLift K hζ γ * q) p hp).continuousAt.eventually_const_lt hhigh
  filter_upwards [sourceKPProductUpper_eventually K p hp, hnear] with x hx hheight
  let Q := q * (ProjGenLinGroup.mk (sourceArchUpperHalfspaceMatrix K hζ x hx), 1)
  have he := productHeight_rational_eq K hζ q γ x hx
  have hQ : sourceKPAdelicOrbitHeight K hζ Q =
      sourceKPAdelicProductHeight K hζ (sourceKPAdelicProjectiveRationalLift K hζ γ * q) x :=
    (sourceKPAdelicOrbitHeight_rational K hζ Q γ).symm.trans
      ((sourceKPAdelicOrbitHeight_eq_cover_of_high K hζ _ (he ▸ hheight)).trans he.symm)
  rw [sourceKPAdelicScalarCutoffProduct, dif_pos hx]
  change Real.smoothTransition (Real.log (sourceKPAdelicOrbitHeight K hζ Q) - Real.log T) = _
  rw [hQ]

theorem sourceKPAdelicScalarCutoffProduct_eventuallyEq_zero_of_low
    {T : ℝ} (hT : 1 < T) (q : SourceKPAdelicProjective K hζ)
    (p : InfinitePlace K → EuclideanSpatial) (hp : ∀ v, 0 < p v 2)
    (hlow : ∀ γ : PGL(2,K),
      sourceKPAdelicProductHeight K hζ (sourceKPAdelicProjectiveRationalLift K hζ γ * q) p ≤ 1) :
    sourceKPAdelicScalarCutoffProduct K hζ T q =ᶠ[𝓝 p] fun _ => 0 := by
  let p₀ : SourceKPProductUpper K := ⟨p, hp⟩
  let Q (x : SourceKPProductUpper K) :=
    q * (ProjGenLinGroup.mk (sourceKPProductUpperSection K hζ x), 1)
  obtain ⟨g, hg⟩ := ProjGenLinGroup.mk_surjective (sourceKPAdelicProjectiveProjection K hζ q)
  let G := sourceKPAdelicProductUpperMatrix K hζ g
  have hproj (x : SourceKPProductUpper K) :
      sourceKPAdelicProjectiveProjection K hζ (Q x) = ProjGenLinGroup.mk (G x) :=
    sourceKPAdelicProductUpperMatrix_projection K hζ q g hg.symm x
  let B := sourceKPAdelicHeightConstant K hζ (G p₀) + 1
  have hB : sourceKPAdelicHeightConstant K hζ (G p₀) < B := lt_add_one _
  have hnear : ∀ᶠ x in 𝓝 p₀, sourceKPAdelicHeightConstant K hζ (G x) < B :=
    ((sourceKPAdelicHeightConstant_continuous K hζ).comp
      (sourceKPAdelicProductUpperMatrix_continuous K hζ g)).continuousAt.eventually_lt_const hB
  obtain ⟨I, hI, hbound⟩ :=
    sourceKPAdelicRationalHeight_finite_of_bound K hζ B (zero_lt_one.trans hT)
  have hsmall : ∀ᶠ x in 𝓝 p₀, ∀ c ∈ I, sourceKPAdelicRationalHeight K hζ (Q x) c < T := by
    apply hI.eventually_all.mpr
    intro c _
    induction c using Quotient.inductionOn with
    | _ γ =>
      have he (x : SourceKPProductUpper K) :
          sourceKPAdelicRationalHeight K hζ (Q x) (sourceKPRationalBorelCosetMk K γ) =
            sourceKPAdelicProductHeight K hζ
              (sourceKPAdelicProjectiveRationalLift K hζ γ * q) x.val :=
        (productHeight_rational_eq K hζ q γ x.val x.property).symm
      change ∀ᶠ x in 𝓝 p₀, sourceKPAdelicRationalHeight K hζ (Q x)
        (sourceKPRationalBorelCosetMk K γ) < T
      simp only [he]
      have hcoe : Tendsto (fun x : SourceKPProductUpper K => x.val) (𝓝 p₀) (𝓝 p) :=
        continuous_subtype_val.continuousAt
      have hheight := (sourceKPAdelicProductHeight_contDiffAt K hζ
        (sourceKPAdelicProjectiveRationalLift K hζ γ * q) p hp).continuousAt.tendsto
      exact (hheight.comp hcoe).eventually_lt_const ((hlow γ).trans_lt hT)
  have hzero : ∀ᶠ x in 𝓝 p₀, sourceKPAdelicScalarCutoffProduct K hζ T q x.val = 0 := by
    filter_upwards [hnear, hsmall] with x hxB hxsmall
    have hH : sourceKPAdelicOrbitHeight K hζ (Q x) ≤ T := by
      apply csSup_le (Set.range_nonempty _)
      rintro _ ⟨γ, rfl⟩
      let c := sourceKPRationalBorelCosetMk K γ
      change sourceKPAdelicRationalHeight K hζ (Q x) c ≤ T
      by_cases hc : c ∈ I
      · exact (hxsmall c hc).le
      · exact le_of_not_gt fun ht => hc (hbound (G x) hxB.le _ (hproj x) c ht)
    rw [sourceKPAdelicScalarCutoffProduct, dif_pos x.property]
    exact Real.smoothTransition.zero_of_nonpos
      (sub_nonpos.mpr (Real.log_le_log (sourceKPAdelicOrbitHeight_pos K hζ (Q x)) hH))
  let S : Set (InfinitePlace K → EuclideanSpatial) := {x | ∀ v, 0 < x v 2}
  have hwithin : ∀ᶠ x in 𝓝[S] p, sourceKPAdelicScalarCutoffProduct K hζ T q x = 0 :=
    (eventually_nhds_subtype_iff S ⟨p, hp⟩
      (fun x => sourceKPAdelicScalarCutoffProduct K hζ T q x = 0)).mp hzero
  have hS : S ∈ 𝓝 p := sourceKPProductUpper_eventually K p hp
  rwa [nhdsWithin_eq_nhds.mpr hS] at hwithin

theorem sourceKPAdelicScalarCutoffProduct_contDiffAt
    {T : ℝ} (hT : 1 < T) (q : SourceKPAdelicProjective K hζ)
    (p : InfinitePlace K → EuclideanSpatial) (hp : ∀ v, 0 < p v 2) :
    ContDiffAt ℝ (∞ : ℕ∞ω) (sourceKPAdelicScalarCutoffProduct K hζ T q) p := by
  by_cases hlow : ∀ γ : PGL(2,K),
      sourceKPAdelicProductHeight K hζ (sourceKPAdelicProjectiveRationalLift K hζ γ * q) p ≤ 1
  · exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      (sourceKPAdelicScalarCutoffProduct_eventuallyEq_zero_of_low K hζ hT q p hp hlow)
  · push_neg at hlow
    obtain ⟨γ, hγ⟩ := hlow
    have hlog := ((sourceKPAdelicProductHeight_contDiffAt K hζ
      (sourceKPAdelicProjectiveRationalLift K hζ γ * q) p hp).log
      (zero_lt_one.trans hγ).ne').sub (contDiffAt_const (c := Real.log T))
    exact (Real.smoothTransition.contDiffAt.comp p hlog).congr_of_eventuallyEq
      (sourceKPAdelicScalarCutoffProduct_eventuallyEq_of_high K hζ T q γ p hp hγ)

theorem sourceKPAdelicScalarCutoffProduct_contDiffOn
    {T : ℝ} (hT : 1 < T) (q : SourceKPAdelicProjective K hζ) :
    ContDiffOn ℝ (∞ : ℕ∞ω) (sourceKPAdelicScalarCutoffProduct K hζ T q)
      {p | ∀ v, 0 < p v 2} :=
  fun p hp => (sourceKPAdelicScalarCutoffProduct_contDiffAt K hζ hT q p hp).contDiffWithinAt

end

end ArtinMatthews
