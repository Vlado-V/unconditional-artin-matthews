module

public import ArtinMatthews.SourceEisensteinHighCompact
public import ArtinMatthews.SourceKPAdelicCuspBand
public import ArtinMatthews.SourceKPCompactTruncatedChart
public import ArtinMatthews.SourceKPAdelicHeightProductChart


set_option backward.privateInPublic true
@[expose] public section

/-! Exact evaluation of the compact high-cusp remainder on a native chart.
A rational translate is chosen with strictly high literal height. -/
namespace ArtinMatthews
open NumberField Matrix Topology Filter SourceHyperbolicGreen SourceArchJacquet OAI.CubicEisenstein
open scoped NumberField MatrixGroups AdeleRing ContDiff
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
local notation "P" => ProductSpace (InfinitePlace K)
local notation "U" => productUpper (InfinitePlace K)
local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "H" => sourceKPAutomorphicCompactOrbitHeight K hζ

private theorem nativeArchHeight_contDiffAt_top (g : GL (Fin 2) ℂ)
    (p : EuclideanSpatial) (hp : 0 < p 2) :
    ContDiffAt ℝ ω (fun x => (sourceArchTranslatedSectionChart 0 g x).re) p := by
  let D := fun x : EuclideanSpatial =>
    quadraticHeightDenominator (Complex.normSq (g 1 0)) ((g 1 0 * star (g 1 1)).re)
      (-(g 1 0 * star (g 1 1)).im) (Complex.normSq (g 1 1)) (x 0) (x 1) (x 2)
  have hD : ContDiff ℝ ω D := by
    dsimp only [D, quadraticHeightDenominator]
    fun_prop
  have hDp : 0 < D p := by
    have h := heightDenominator_pos ((p 0 : ℂ) + (p 1 : ℂ) * Complex.I) (p 2) hp
      (sourceArchTranslatedRow g) (sourceArchTranslatedRow_ne_zero g)
    rw [heightDenominator_eq_quadratic] at h
    simpa only [D, sourceArchTranslatedRow] using h
  have hy : ContDiffAt ℝ ω (fun x : EuclideanSpatial => x 2) p := by fun_prop
  have hprofile : ContDiffAt ℝ ω (sourceArchTranslatedProfile 0 g) p := by
    unfold sourceArchTranslatedProfile spatialHeightPower logRatioPower
    exact contDiffAt_const.mul (contDiffAt_const.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp p
      ((hy.log hp.ne').sub (hD.contDiffAt.log hDp.ne')))).cexp
  exact Complex.reCLM.contDiff.contDiffAt.comp p (hprofile.congr_of_eventuallyEq
    (sourceArchTranslatedSectionChart_eventually_profile 0 g p hp))

private theorem nativeProductHeight_contDiffAt_top (q : SourceKPAdelicProjective K hζ)
    (p : P) (hp : ∀ v, 0 < p v 2) :
    ContDiffAt ℝ ω (sourceKPAdelicProductHeight K hζ q) p := by
  rcases q with ⟨a,qf⟩
  obtain ⟨g,rfl⟩ := ProjGenLinGroup.mk_surjective a
  obtain ⟨u,hu⟩ := ProjGenLinGroup.mk_surjective (sourceKPFiniteAdeleProjectiveProjection K hζ qf)
  let localMatrix := fun v => sourceKPArchMatrixComplexEquiv K hζ v (sourceArchGLPiEquiv K g v)
  have hprod : ContDiffAt ℝ ω (fun x : P =>
      ∏ v, (sourceArchTranslatedSectionChart 0 (localMatrix v) (x v)).re^v.mult) p := by
    apply contDiffAt_prod
    intro v _
    have hev : ContDiffAt ℝ ω (fun x : P => x v) p := by fun_prop
    exact ((nativeArchHeight_contDiffAt_top (localMatrix v) (p v) (hp v)).comp p hev).pow v.mult
  apply (hprod.mul (contDiffAt_const (c := sourceKPFiniteMatrixHeightProduct K u))).congr_of_eventuallyEq
  filter_upwards [sourceKPProductUpper_eventually K p hp] with x hx
  exact sourceKPAdelicProductHeight_factor K hζ g qf u hu.symm x hx

theorem sourceKPCompactHighNonconstantEisenstein_adelic (s : ℂ) (T : ℝ) (hT : 1 < T)
    (q : SourceKPAdelicProjective K hζ) (hq : T < sourceKPAdelicCoverHeight K hζ q) :
    sourceKPCompactHighNonconstantEisenstein K hζ s T hT
      (sourceKPCompactHighCuspMk K hζ T
        (sourceKPHighCuspProjection K hζ T ⟨sourceKPFiniteLevelMk K hζ q,hq⟩)) =
      sourceKPAdelicNonconstantEisenstein K hζ s q := by
  rw [sourceKPCompactHighNonconstantEisenstein_mk,sourceKPHighCuspNonconstantEisenstein_rep]
  exact sourceKPFiniteLevelNonconstantEisenstein_mk K hζ s q

theorem sourceKPCompactHighNonconstantEnergy_adelic {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (T : ℝ) (hT : 1 < T) (q : SourceKPAdelicProjective K hζ)
    (hq : T < sourceKPAdelicCoverHeight K hζ q) :
    sourceKPCompactHighNonconstantEnergy K hζ hs T hT
      (sourceKPCompactHighCuspMk K hζ T
        (sourceKPHighCuspProjection K hζ T ⟨sourceKPFiniteLevelMk K hζ q,hq⟩)) =
      sourceKPAdelicNonconstantEnergy K hζ s q := by
  rw [sourceKPCompactHighNonconstantEnergy_mk]
  exact sourceKPHighCuspNonconstantEnergy_adelic K hζ hs T hT _ q rfl

theorem sourceKPUpperToCompact_native_adelic (qf : SourceKPFiniteAdeleProjective K hζ)
    (p : P) (hp : p ∈ U) :
    sourceKPUpperToCompact K hζ (QuotientGroup.mk qf) (sourceKPArchEuclideanUpperMap K p) =
      sourceKPAutomorphicCompactMk K hζ (sourceKPAutomorphicLevelMk K hζ
        ((1,qf)*(ProjGenLinGroup.mk (sourceArchUpperHalfspaceMatrix K hζ p (fun v => productUpper_pos hp v)),1))) :=
  sourceKPUpperToCompact_product_point K hζ qf p hp

theorem sourceKPUpperToCompact_height_eventuallyEq
    (qf : SourceKPFiniteAdeleProjective K hζ) (γ : PGL(2,K)) (p : P) (hp : p ∈ U)
    (hγ : 1 < sourceKPAdelicProductHeight K hζ (sourceKPAdelicProjectiveRationalLift K hζ γ*(1,qf)) p) :
    (fun x => H (sourceKPUpperToCompact K hζ (QuotientGroup.mk qf) (sourceKPArchEuclideanUpperMap K x))) =ᶠ[𝓝 p]
      sourceKPAdelicProductHeight K hζ (sourceKPAdelicProjectiveRationalLift K hζ γ*(1,qf)) := by
  let Q := sourceKPAdelicProjectiveRationalLift K hζ γ*(1,qf)
  have hnear := (sourceKPAdelicProductHeight_contDiffAt K hζ Q p
    (fun v => productUpper_pos hp v)).continuousAt.eventually_const_lt hγ
  filter_upwards [(productUpper_isOpen (InfinitePlace K)).mem_nhds hp,hnear] with x hx hheight
  let a := ProjGenLinGroup.mk (sourceArchUpperHalfspaceMatrix K hζ x (fun v => productUpper_pos hx v))
  let q : SourceKPAdelicProjective K hζ := (1,qf)*(a,1)
  have hcover : sourceKPAdelicProductHeight K hζ Q x =
      sourceKPAdelicCoverHeight K hζ (sourceKPAdelicProjectiveRationalLift K hζ γ*q) := by
    dsimp only [Q,q]
    rw [sourceKPAdelicProductHeight,dite_eq_left (fun v => productUpper_pos hx v),mul_assoc]
  rw [sourceKPUpperToCompact_native_adelic K hζ qf x hx,sourceKPAutomorphicCompactOrbitHeight_mk,
    sourceKPAutomorphicOrbitHeight_mk]
  change sourceKPAdelicOrbitHeight K hζ q = _
  exact (sourceKPAdelicOrbitHeight_rational K hζ q γ).symm.trans
    ((sourceKPAdelicOrbitHeight_eq_cover_of_high K hζ _ (hcover ▸ hheight)).trans hcover.symm)

theorem sourceKPUpperToCompact_height_eventuallyEq_of_high
    (qf : SourceKPFiniteAdeleProjective K hζ) (p : P) (hp : p ∈ U)
    (hhigh : 1 < H (sourceKPUpperToCompact K hζ (QuotientGroup.mk qf) (sourceKPArchEuclideanUpperMap K p))) :
    ∃ γ : PGL(2,K), (fun x => H (sourceKPUpperToCompact K hζ (QuotientGroup.mk qf)
        (sourceKPArchEuclideanUpperMap K x))) =ᶠ[𝓝 p]
      sourceKPAdelicProductHeight K hζ (sourceKPAdelicProjectiveRationalLift K hζ γ*(1,qf)) := by
  let q : SourceKPAdelicProjective K hζ :=
    (1,qf)*(ProjGenLinGroup.mk (sourceArchUpperHalfspaceMatrix K hζ p (fun v => productUpper_pos hp v)),1)
  have hc : sourceKPUpperToCompact K hζ (QuotientGroup.mk qf) (sourceKPArchEuclideanUpperMap K p) =
      sourceKPAutomorphicCompactMk K hζ (sourceKPAutomorphicLevelMk K hζ q) :=
    sourceKPUpperToCompact_native_adelic K hζ qf p hp
  rw [hc,sourceKPAutomorphicCompactOrbitHeight_mk,sourceKPAutomorphicOrbitHeight_mk] at hhigh
  obtain ⟨_,⟨γ,rfl⟩,hγ⟩ := exists_lt_of_lt_csSup (Set.range_nonempty _) hhigh
  refine ⟨γ,sourceKPUpperToCompact_height_eventuallyEq K hζ qf γ p hp ?_⟩
  rw [sourceKPAdelicProductHeight,dite_eq_left (fun v => productUpper_pos hp v),mul_assoc]
  exact hγ

def sourceKPCompactCore_of_supported_chart {n : ℕ∞ω} (F : Y → ℂ)
    (hc : HasCompactSupport F)
    (hdiff : ∀ b, ContDiffOn ℝ n (sourceKPCompactChartPullback K hζ F b) U) :
    sourceKPCompactCore K hζ n := by
  refine ⟨F,?_,hc,hdiff⟩
  apply continuous_iff_continuousAt.mpr
  intro y
  obtain ⟨b,p,rfl⟩ := sourceKPUpperToCompact_cover K hζ y
  let m := sourceKPUpperToCompact K hζ b
  have hpos (q : SourceKPArchUpperHalfSpace K) : sourceKPArchUpperEuclideanMap K q ∈ U :=
    fun v _ => sourceKPArchUpperEuclidean_positive K q v
  have hcont := (hdiff b).continuousOn.comp_continuous (sourceKPArchUpperEuclideanMap_continuous K) hpos
  have he : F ∘ m = sourceKPCompactChartPullback K hζ F b ∘ sourceKPArchUpperEuclideanMap K := by
    funext q
    simp only [m,Function.comp_apply,sourceKPCompactChartPullback_of_positive K hζ F b _ (hpos q),
      sourceKPArchUpperEuclideanMap_left_inverse]
  have hm : Continuous (F ∘ m) := he.symm ▸ hcont
  have hn : Filter.map m (𝓝 p) = 𝓝 (m p) :=
    (sourceKPUpperToCompact_isOpenMap K hζ b).map_nhds_eq
      (sourceKPUpperToCompact_continuous K hζ b).continuousAt
  change Tendsto F (𝓝 (m p)) (𝓝 (F (m p)))
  rw [← hn,tendsto_map'_iff]
  exact hm.continuousAt

def sourceKPCompactHighLocalizedRemainder (s : ℂ) (T : ℝ) (hT : 1 < T) (ρ : ℝ → ℝ) : Y → ℂ :=
  Function.extend Subtype.val (fun x : SourceKPCompactHighCusp K hζ T =>
    (ρ (H x.val) : ℂ)*sourceKPCompactHighNonconstantEisenstein K hζ s T hT x) (fun _ => 0)

theorem sourceKPCompactHighLocalizedRemainder_apply (s : ℂ) (T : ℝ) (hT : 1 < T) (ρ : ℝ → ℝ)
    (x : SourceKPCompactHighCusp K hζ T) :
    sourceKPCompactHighLocalizedRemainder K hζ s T hT ρ x.val =
      (ρ (H x.val) : ℂ)*sourceKPCompactHighNonconstantEisenstein K hζ s T hT x :=
  Subtype.val_injective.extend_apply _ _ x

theorem sourceKPCompactHighLocalizedRemainder_zero_of_low (s : ℂ) (T : ℝ) (hT : 1 < T)
    (ρ : ℝ → ℝ) (y : Y) (hy : H y ≤ T) :
    sourceKPCompactHighLocalizedRemainder K hζ s T hT ρ y = 0 := by
  apply Function.extend_apply'
  rintro ⟨x,rfl⟩
  exact (not_lt_of_ge hy) x.property

theorem sourceKPCompactHighLocalizedRemainder_zero_of_weight (s : ℂ) (T : ℝ) (hT : 1 < T)
    (ρ : ℝ → ℝ) (y : Y) (hy : ρ (H y) = 0) :
    sourceKPCompactHighLocalizedRemainder K hζ s T hT ρ y = 0 := by
  by_cases h : T < H y
  · have he := sourceKPCompactHighLocalizedRemainder_apply K hζ s T hT ρ ⟨y,h⟩
    change sourceKPCompactHighLocalizedRemainder K hζ s T hT ρ y = _ at he
    rw [he]
    simp only [hy,Complex.ofReal_zero,zero_mul]
  · apply Function.extend_apply'
    rintro ⟨a,rfl⟩
    exact h a.property

theorem sourceKPCompactHighLocalizedRemainder_chart_eventuallyEq (s : ℂ) (T : ℝ) (hT : 1 < T)
    (ρ : ℝ → ℝ) (qf : SourceKPFiniteAdeleProjective K hζ)
    (γ : PGL(2,K)) (p : P) (hp : p ∈ U)
    (hγ : T < sourceKPAdelicProductHeight K hζ (sourceKPAdelicProjectiveRationalLift K hζ γ*(1,qf)) p) :
    sourceKPCompactChartPullback K hζ (sourceKPCompactHighLocalizedRemainder K hζ s T hT ρ)
      (QuotientGroup.mk qf) =ᶠ[𝓝 p] fun x =>
        (ρ (sourceKPAdelicProductHeight K hζ (sourceKPAdelicProjectiveRationalLift K hζ γ*(1,qf)) x) : ℂ) *
          sourceKPAdelicNonconstantProductChart K hζ s (sourceKPAdelicProjectiveRationalLift K hζ γ*(1,qf)) x := by
  let Q := sourceKPAdelicProjectiveRationalLift K hζ γ*(1,qf)
  have hnear := (sourceKPAdelicProductHeight_contDiffAt K hζ Q p
    (fun v => productUpper_pos hp v)).continuousAt.eventually_const_lt hγ
  filter_upwards [(productUpper_isOpen (InfinitePlace K)).mem_nhds hp,hnear] with x hx hheight
  let a := ProjGenLinGroup.mk (sourceArchUpperHalfspaceMatrix K hζ x (fun v => productUpper_pos hx v))
  let q := Q*(a,1)
  have hcover : sourceKPAdelicProductHeight K hζ Q x = sourceKPAdelicCoverHeight K hζ q := by
    rw [sourceKPAdelicProductHeight,dite_eq_left (fun v => productUpper_pos hx v)]
  have hq : T < sourceKPAdelicCoverHeight K hζ q := hcover ▸ hheight
  let z := sourceKPCompactHighCuspMk K hζ T
    (sourceKPHighCuspProjection K hζ T ⟨sourceKPFiniteLevelMk K hζ q,hq⟩)
  have hz : z.val = sourceKPUpperToCompact K hζ (QuotientGroup.mk qf) (sourceKPArchEuclideanUpperMap K x) := by
    rw [sourceKPUpperToCompact_native_adelic K hζ qf x hx]
    change sourceKPAutomorphicCompactMk K hζ (sourceKPAutomorphicLevelMk K hζ q) = _
    dsimp only [q,Q]
    rw [mul_assoc,sourceKPAutomorphicLevelMk_rational]
  have hH : H z.val = sourceKPAdelicCoverHeight K hζ q := by
    change sourceKPAutomorphicOrbitHeight K hζ (sourceKPAutomorphicLevelMk K hζ q) = _
    rw [sourceKPAutomorphicOrbitHeight_mk,sourceKPAdelicOrbitHeight_eq_cover_of_high K hζ q (hT.trans hq)]
  change sourceKPCompactChartPullback K hζ (sourceKPCompactHighLocalizedRemainder K hζ s T hT ρ)
    (QuotientGroup.mk qf) x = (ρ (sourceKPAdelicProductHeight K hζ Q x) : ℂ) *
      sourceKPAdelicNonconstantProductChart K hζ s Q x
  rw [sourceKPCompactChartPullback_of_positive K hζ _ (QuotientGroup.mk qf) x hx,← hz,
    sourceKPCompactHighLocalizedRemainder_apply K hζ s T hT ρ z,hH,hcover,
    sourceKPAdelicNonconstantProductChart_apply_of_positive K hζ s Q x (fun v => productUpper_pos hx v)]
  exact congrArg (fun r : ℂ => (ρ (sourceKPAdelicCoverHeight K hζ q) : ℂ)*r)
    (sourceKPCompactHighNonconstantEisenstein_adelic K hζ s T hT q hq)

end
end ArtinMatthews

/-! A smooth literal height weight supported strictly in the high cusp
localizes the actual remainder to the compact test core. -/
namespace ArtinMatthews
open NumberField Matrix Topology Filter Set SourceHyperbolicGreen OAI.CubicEisenstein
open scoped NumberField MatrixGroups AdeleRing ContDiff
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
local notation "P" => ProductSpace (InfinitePlace K)
local notation "U" => productUpper (InfinitePlace K)
local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "H" => sourceKPAutomorphicCompactOrbitHeight K hζ

theorem sourceKPCompactHighLocalizedRemainder_support (s : ℂ) (T L B : ℝ)
    (hT : 1 < T) (hTL : T < L) (hLB : L ≤ B)
    (ρ : ℝ → ℝ) (hρ : ∀ h ∉ Icc L B, 0 < h → ρ h = 0) :
    tsupport (sourceKPCompactHighLocalizedRemainder K hζ s T hT ρ) ⊆ {y : Y | H y ∈ Icc L B} := by
  have hS := sourceKPAutomorphicCompactHighBand_isCompact K hζ L B (hT.trans hTL) hLB
  apply closure_minimal _ hS.isClosed
  intro y hy
  by_contra hy'
  exact hy (sourceKPCompactHighLocalizedRemainder_zero_of_weight K hζ s T hT ρ y (hρ _ hy' (sourceKPAutomorphicCompactOrbitHeight_pos K hζ y)))

theorem sourceKPCompactHighLocalizedRemainder_chart_contDiff {n : ℕ∞ω} (s : ℂ) (T L B : ℝ)
    (hT : 1 < T) (hTL : T < L) (hLB : L ≤ B)
    (ρ : ℝ → ℝ) (hρ : ContDiffOn ℝ n ρ (Ioi 0))
    (hzero : ∀ h ∉ Icc L B, 0 < h → ρ h = 0)
    (hR : ∀ (q : SourceKPAdelicProjective K hζ) (p : P), p ∈ U →
      ContDiffAt ℝ n (sourceKPAdelicNonconstantProductChart K hζ s q) p)
    (b : SourceKPFiniteLevelFiber K hζ) :
    ContDiffOn ℝ n (sourceKPCompactChartPullback K hζ
      (sourceKPCompactHighLocalizedRemainder K hζ s T hT ρ) b) U := by
  obtain ⟨qf,rfl⟩ := Quotient.mk_surjective b
  intro p hp
  let c := sourceKPUpperToCompact K hζ (QuotientGroup.mk qf) ∘ sourceKPArchEuclideanUpperMap K
  let F := sourceKPCompactHighLocalizedRemainder K hζ s T hT ρ
  let S : Set Y := {y | H y ∈ Icc L B}
  have hS : IsCompact S := sourceKPAutomorphicCompactHighBand_isCompact K hζ L B (hT.trans hTL) hLB
  by_cases hband : c p ∈ S
  · have hH : T < H (c p) := hTL.trans_le hband.1
    obtain ⟨γ,hEq⟩ := sourceKPUpperToCompact_height_eventuallyEq_of_high K hζ qf p hp (hT.trans hH)
    let Q := sourceKPAdelicProjectiveRationalLift K hζ γ*(1,qf)
    have hheight : T < sourceKPAdelicProductHeight K hζ Q p := hEq.eq_of_nhds ▸ hH
    have hρp := (hρ (sourceKPAdelicProductHeight K hζ Q p)
      ((zero_lt_one.trans hT).trans hheight)).contDiffAt
        (Ioi_mem_nhds ((zero_lt_one.trans hT).trans hheight))
    have hprod : ContDiffAt ℝ n (sourceKPAdelicProductHeight K hζ Q) p :=
      (nativeProductHeight_contDiffAt_top K hζ Q p (fun v => productUpper_pos hp v)).of_le le_top
    have hval : ContDiffAt ℝ n (fun x => (ρ (sourceKPAdelicProductHeight K hζ Q x) : ℂ)) p :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp p (hρp.comp p hprod)
    exact ((hval.mul (hR Q p hp)).congr_of_eventuallyEq
      (sourceKPCompactHighLocalizedRemainder_chart_eventuallyEq K hζ s T hT ρ qf γ p hp hheight)).contDiffWithinAt
  · have hc : ContinuousAt c p :=
      (sourceKPUpperToCompact_continuous K hζ (QuotientGroup.mk qf)).continuousAt.comp
        ((sourceKPArchEuclideanUpperMap_continuousOn K p hp).continuousAt
          ((productUpper_isOpen (InfinitePlace K)).mem_nhds hp))
    have hout : ∀ᶠ x in 𝓝 p, c x ∉ S := hc.eventually (hS.isClosed.isOpen_compl.mem_nhds hband)
    have he : sourceKPCompactChartPullback K hζ F (QuotientGroup.mk qf) =ᶠ[𝓝 p]
        fun _ => (0 : ℂ) := by
      filter_upwards [hout,(productUpper_isOpen (InfinitePlace K)).mem_nhds hp] with x hx hxU
      change sourceKPCompactChartPullback K hζ F (QuotientGroup.mk qf) x = 0
      rw [sourceKPCompactChartPullback_of_positive K hζ F (QuotientGroup.mk qf) x hxU]
      exact sourceKPCompactHighLocalizedRemainder_zero_of_weight K hζ s T hT ρ (c x)
        (hzero _ hx (sourceKPAutomorphicCompactOrbitHeight_pos K hζ (c x)))
    exact ((contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq he).contDiffWithinAt

def sourceKPCompactHighLocalizedRemainderCore {n : ℕ∞ω} (s : ℂ) (T L B : ℝ)
    (hT : 1 < T) (hTL : T < L) (hLB : L ≤ B)
    (ρ : ℝ → ℝ) (hρ : ContDiffOn ℝ n ρ (Ioi 0))
    (hzero : ∀ h ∉ Icc L B, 0 < h → ρ h = 0)
    (hR : ∀ (q : SourceKPAdelicProjective K hζ) (p : P), p ∈ U →
      ContDiffAt ℝ n (sourceKPAdelicNonconstantProductChart K hζ s q) p) :
    sourceKPCompactCore K hζ n := by
  let F := sourceKPCompactHighLocalizedRemainder K hζ s T hT ρ
  have hs := sourceKPCompactHighLocalizedRemainder_support K hζ s T L B hT hTL hLB ρ hzero
  have hS := sourceKPAutomorphicCompactHighBand_isCompact K hζ L B (hT.trans hTL) hLB
  have hdiff := sourceKPCompactHighLocalizedRemainder_chart_contDiff K hζ s T L B hT hTL hLB ρ hρ hzero hR
  exact sourceKPCompactCore_of_supported_chart K hζ F
    (hS.of_isClosed_subset (isClosed_tsupport _) hs) hdiff

theorem sourceKPCompactHighLocalizedRemainderCore_apply {n : ℕ∞ω} (s : ℂ) (T L B : ℝ)
    (hT : 1 < T) (hTL : T < L) (hLB : L ≤ B)
    (ρ : ℝ → ℝ) (hρ : ContDiffOn ℝ n ρ (Ioi 0))
    (hzero : ∀ h ∉ Icc L B, 0 < h → ρ h = 0)
    (hR : ∀ (q : SourceKPAdelicProjective K hζ) (p : P), p ∈ U →
      ContDiffAt ℝ n (sourceKPAdelicNonconstantProductChart K hζ s q) p) (y : Y) :
    (sourceKPCompactHighLocalizedRemainderCore K hζ s T L B hT hTL hLB ρ hρ hzero hR).val y =
      sourceKPCompactHighLocalizedRemainder K hζ s T hT ρ y := rfl

end
end ArtinMatthews

/-! A smooth real weight in the literal high height coordinate is an
actual compact test on the automorphic quotient. -/
namespace ArtinMatthews
open NumberField Matrix Topology Filter Set SourceHyperbolicGreen OAI.CubicEisenstein
open scoped NumberField MatrixGroups AdeleRing ContDiff
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
local notation "P" => ProductSpace (InfinitePlace K)
local notation "U" => productUpper (InfinitePlace K)
local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "H" => sourceKPAutomorphicCompactOrbitHeight K hζ

theorem sourceKPCompactHeightProfile_chart_contDiff {n : ℕ∞ω}
    (L B : ℝ) (hL : 1 < L) (hLB : L ≤ B)
    (ρ : ℝ → ℝ) (hρ : ContDiffOn ℝ n ρ (Ioi 0))
    (hzero : ∀ h ∉ Icc L B, 0 < h → ρ h = 0)
    (b : SourceKPFiniteLevelFiber K hζ) :
    ContDiffOn ℝ n (sourceKPCompactChartPullback K hζ (fun y => (ρ (H y) : ℂ)) b) U := by
  obtain ⟨qf,rfl⟩ := Quotient.mk_surjective b
  intro p hp
  let c := sourceKPUpperToCompact K hζ (QuotientGroup.mk qf) ∘ sourceKPArchEuclideanUpperMap K
  let F : Y → ℂ := fun y => (ρ (H y) : ℂ)
  let S : Set Y := {y | H y ∈ Icc L B}
  have hS : IsCompact S := sourceKPAutomorphicCompactHighBand_isCompact K hζ L B hL hLB
  by_cases hband : c p ∈ S
  · have hH : 1 < H (c p) := hL.trans_le hband.1
    obtain ⟨γ,hEq⟩ := sourceKPUpperToCompact_height_eventuallyEq_of_high K hζ qf p hp hH
    let Q := sourceKPAdelicProjectiveRationalLift K hζ γ*(1,qf)
    have hheight : 1 < sourceKPAdelicProductHeight K hζ Q p := hEq.eq_of_nhds ▸ hH
    have hpheight := zero_lt_one.trans hheight
    have hρp := (hρ (sourceKPAdelicProductHeight K hζ Q p) hpheight).contDiffAt (Ioi_mem_nhds hpheight)
    have hprod : ContDiffAt ℝ n (sourceKPAdelicProductHeight K hζ Q) p :=
      (nativeProductHeight_contDiffAt_top K hζ Q p (fun v => productUpper_pos hp v)).of_le le_top
    have hval : ContDiffAt ℝ n (fun x => (ρ (sourceKPAdelicProductHeight K hζ Q x) : ℂ)) p :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp p (hρp.comp p hprod)
    have he : sourceKPCompactChartPullback K hζ F (QuotientGroup.mk qf) =ᶠ[𝓝 p]
        fun x => (ρ (sourceKPAdelicProductHeight K hζ Q x) : ℂ) := by
      filter_upwards [(productUpper_isOpen (InfinitePlace K)).mem_nhds hp,
        hEq] with x hx hxx
      change sourceKPCompactChartPullback K hζ F (QuotientGroup.mk qf) x =
        (ρ (sourceKPAdelicProductHeight K hζ Q x) : ℂ)
      rw [sourceKPCompactChartPullback_of_positive K hζ F (QuotientGroup.mk qf) x hx]
      exact congrArg (fun h : ℝ => (ρ h : ℂ)) hxx
    exact (hval.congr_of_eventuallyEq he).contDiffWithinAt
  · have hc : ContinuousAt c p :=
      (sourceKPUpperToCompact_continuous K hζ (QuotientGroup.mk qf)).continuousAt.comp
        ((sourceKPArchEuclideanUpperMap_continuousOn K p hp).continuousAt
          ((productUpper_isOpen (InfinitePlace K)).mem_nhds hp))
    have hout : ∀ᶠ x in 𝓝 p, c x ∉ S := hc.eventually (hS.isClosed.isOpen_compl.mem_nhds hband)
    have he : sourceKPCompactChartPullback K hζ F (QuotientGroup.mk qf) =ᶠ[𝓝 p] fun _ => (0 : ℂ) := by
      filter_upwards [hout,(productUpper_isOpen (InfinitePlace K)).mem_nhds hp] with x hx hxU
      change sourceKPCompactChartPullback K hζ F (QuotientGroup.mk qf) x = 0
      rw [sourceKPCompactChartPullback_of_positive K hζ F (QuotientGroup.mk qf) x hxU]
      exact Complex.ofReal_eq_zero.mpr (hzero _ hx (sourceKPAutomorphicCompactOrbitHeight_pos K hζ (c x)))
    exact ((contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq he).contDiffWithinAt

def sourceKPCompactHeightProfileCore {n : ℕ∞ω}
    (L B : ℝ) (hL : 1 < L) (hLB : L ≤ B)
    (ρ : ℝ → ℝ) (hρ : ContDiffOn ℝ n ρ (Ioi 0))
    (hzero : ∀ h ∉ Icc L B, 0 < h → ρ h = 0) : sourceKPCompactCore K hζ n := by
  let F : Y → ℂ := fun y => (ρ (H y) : ℂ)
  have hdiff := sourceKPCompactHeightProfile_chart_contDiff K hζ L B hL hLB ρ hρ hzero
  have hS := sourceKPAutomorphicCompactHighBand_isCompact K hζ L B hL hLB
  have hs : Function.support F ⊆ {y : Y | H y ∈ Icc L B} := by
    intro y hy
    by_contra hx
    exact hy (Complex.ofReal_eq_zero.mpr (hzero _ hx (sourceKPAutomorphicCompactOrbitHeight_pos K hζ y)))
  exact sourceKPCompactCore_of_supported_chart K hζ F
    (HasCompactSupport.of_support_subset_isCompact hS hs) hdiff

end
end ArtinMatthews
