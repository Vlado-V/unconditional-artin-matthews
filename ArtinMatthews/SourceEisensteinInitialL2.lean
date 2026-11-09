module

public import ArtinMatthews.SourceEisensteinNativeWeakLocal
public import ArtinMatthews.SourceEisensteinHighCompactChart
public import ArtinMatthews.SourceEisensteinHighShellRecurrence
public import ArtinMatthews.SourceKPAdelicEisensteinProductC2
public import ArtinMatthews.SourceKPCompactSupportedWeakTest
public import ArtinMatthews.SourceHyperbolicCaccioppoli
public import ArtinMatthews.SourceKPCompactTruncatedL2Join


set_option backward.privateInPublic true
@[expose] public section

/-! On the open plateau of a high-cusp localization the actual remainder
satisfies the native tested eigen-equation. A compact test is localized
to finitely many neighborhoods with literal high rational representatives. -/
namespace ArtinMatthews
open NumberField Matrix Topology MeasureTheory Filter Set SourceHyperbolicGreen OAI.CubicEisenstein
open scoped NumberField MatrixGroups AdeleRing ContDiff
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
local notation "P" => ProductSpace (InfinitePlace K)
local notation "U" => productUpper (InfinitePlace K)
local notation "H" => sourceKPAutomorphicCompactOrbitHeight K hζ
local notation "μ" => productVolume (InfinitePlace K)

theorem sourceKPCompactHighLocalizedRemainder_weak_native {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (T A B : ℝ) (hT : 1 < T) (hTA : T ≤ A)
    (ρ : ℝ → ℝ) (hρ : ∀ h ∈ Ioo A B, ρ h = 1)
    (b : SourceKPFiniteLevelFiber K hζ)
    (hreg : ContDiffOn ℝ 1 (sourceKPCompactChartPullback K hζ
      (sourceKPCompactHighLocalizedRemainder K hζ s T hT ρ) b) U)
    (φ : h1Tests (InfinitePlace K) 2)
    (hφ : ∀ p ∈ tsupport (φ).val,
      H (sourceKPUpperToCompact K hζ b (sourceKPArchEuclideanUpperMap K p)) ∈ Ioo A B) :
    let v := sourceKPCompactChartPullback K hζ (sourceKPCompactHighLocalizedRemainder K hζ s T hT ρ) b
    (∫ x, productGradientPair (φ).val v x ∂μ) =
      (InfinitePlace.nrComplexPlaces K : ℂ)*(1-4*s^2)*(∫ x, star ((φ).val x)*v x ∂μ) := by
  obtain ⟨qf,rfl⟩ := Quotient.mk_surjective b
  dsimp only
  let v := sourceKPCompactChartPullback K hζ (sourceKPCompactHighLocalizedRemainder K hζ s T hT ρ)
    (QuotientGroup.mk qf)
  apply sourceProductWeakEigen_of_support_neighborhoods K v
    ((InfinitePlace.nrComplexPlaces K : ℂ)*(1-4*s^2)) (fun p hp =>
      (hreg p hp).contDiffAt ((productUpper_isOpen (InfinitePlace K)).mem_nhds hp)) φ
  intro p hp
  have hpU := (φ).prop.2.2 hp
  have hHeight := hφ p hp
  have hhigh : 1 < H (sourceKPUpperToCompact K hζ (QuotientGroup.mk qf) (sourceKPArchEuclideanUpperMap K p)) :=
    hT.trans (hTA.trans_lt hHeight.1)
  obtain ⟨γ,hEq⟩ := sourceKPUpperToCompact_height_eventuallyEq_of_high K hζ qf p hpU hhigh
  let Q := sourceKPAdelicProjectiveRationalLift K hζ γ*(1,qf)
  let G := sourceKPAdelicProductHeight K hζ Q
  have hE : H (sourceKPUpperToCompact K hζ (QuotientGroup.mk qf) (sourceKPArchEuclideanUpperMap K p)) = G p :=
    hEq.eq_of_nhds
  let O := U ∩ G ⁻¹' Ioo A B
  have hGc : ContinuousOn G U := fun x hx =>
    (sourceKPAdelicProductHeight_contDiffAt K hζ Q x (fun w => productUpper_pos hx w)).continuousAt.continuousWithinAt
  have hO : IsOpen O := hGc.isOpen_inter_preimage (productUpper_isOpen (InfinitePlace K)) isOpen_Ioo
  have hpoint : p ∈ O := by
    refine ⟨hpU,?_⟩
    change G p ∈ Ioo A B
    rw [← hE]
    exact hHeight
  let R := sourceKPAdelicNonconstantProductChart K hζ s Q
  have he : Set.EqOn v R O := by
    intro x hx
    have hxG : G x ∈ Ioo A B := hx.2
    have hγx : T < G x := hTA.trans_lt hxG.1
    have h := (sourceKPCompactHighLocalizedRemainder_chart_eventuallyEq K hζ s T hT ρ qf γ x hx.1 hγx).eq_of_nhds
    change v x = (ρ (G x) : ℂ)*R x at h
    rwa [hρ _ hxG,Complex.ofReal_one,one_mul] at h
  refine ⟨O,hO,hpoint,fun _ hx => hx.1,?_⟩
  intro ψ hψ
  have hmass : (∫ x, star (ψ.val x)*v x ∂μ) = ∫ x, star (ψ.val x)*R x ∂μ := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      change star (ψ.val x)*v x = star (ψ.val x)*R x
      by_cases hx : x ∈ tsupport ψ.val
      · rw [he (hψ hx)]
      · rw [image_eq_zero_of_notMem_tsupport hx,star_zero,zero_mul,zero_mul]
  rw [sourceProductGradientPair_test_congr K ψ hO hψ he,hmass]
  exact sourceKPAdelicNonconstantProductChart_gradient_eigen K hζ hs Q ψ.prop.1 ψ.prop.2.1 ψ.prop.2.2

end
end ArtinMatthews

/-! The square-cutoff remainder is a genuine compact C2 test. A second,
larger cutoff is identically one on an open neighborhood of its support. -/
namespace ArtinMatthews
open NumberField Matrix Topology Set Filter SourceHyperbolicGreen OAI.CubicEisenstein
open scoped NumberField MatrixGroups AdeleRing ContDiff
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
local notation "P" => ProductSpace (InfinitePlace K)
local notation "U" => productUpper (InfinitePlace K)
local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "H" => sourceKPAutomorphicCompactOrbitHeight K hζ

theorem sourceKPAdelicNonconstantProductChart_contDiffAt_two {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (q : SourceKPAdelicProjective K hζ) (p : P) (hp : p ∈ U) :
    ContDiffAt ℝ 2 (sourceKPAdelicNonconstantProductChart K hζ s q) p := by
  have hs₀ : 0 < s.re := by
    push_cast at hs
    have hn : 0 ≤ (Module.finrank ℚ K : ℝ) := Nat.cast_nonneg _
    linarith
  exact (sourceKPAdelicEisensteinProductChart_contDiffAt_two K hζ hs q p
    (fun v => productUpper_pos hp v)).sub
      (((sourceKPAdelicProductSection_contDiffAt K hζ s q p (fun v => productUpper_pos hp v)).of_le
        (by simp)).add ((sourceKPAdelicOutgoingProductChart_contDiffAt K hζ hs₀ q p hp).of_le (by simp)))

def sourceCuspRemainderPlateauWeight (T L x : ℝ) : ℝ :=
  Real.smoothTransition ((x-(T+L)/2)/((L-T)/4)) *
    Real.smoothTransition ((16*L-x)/(4*L))

theorem sourceCuspRemainderPlateauWeight_contDiff (T L : ℝ) :
    ContDiff ℝ (∞ : ℕ∞ω) (sourceCuspRemainderPlateauWeight T L) :=
  (Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)).mul
    (Real.smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).div_const _))

theorem sourceCuspRemainderPlateauWeight_one (T L x : ℝ) (hL : 0 < L) (hTL : T < L)
    (hx : x ∈ Icc ((T+3*L)/4) (12*L)) : sourceCuspRemainderPlateauWeight T L x = 1 := by
  have hlo : 1 ≤ (x-(T+L)/2)/((L-T)/4) := by
    apply (le_div_iff₀ (by linarith : 0 < (L-T)/4)).mpr
    linarith [hx.1]
  have hhi : 1 ≤ (16*L-x)/(4*L) := by
    apply (le_div_iff₀ (by positivity : 0 < 4*L)).mpr
    linarith [hx.2]
  rw [sourceCuspRemainderPlateauWeight,Real.smoothTransition.one_of_one_le hlo,
    Real.smoothTransition.one_of_one_le hhi,one_mul]

theorem sourceCuspRemainderPlateauWeight_zero (T L x : ℝ) (hL : 0 < L) (hTL : T < L)
    (hx : x ∉ Icc ((T+L)/2) (16*L)) : sourceCuspRemainderPlateauWeight T L x = 0 := by
  by_cases h₁ : (T+L)/2 ≤ x
  · have h₂ : 16*L < x := lt_of_not_ge (fun h => hx ⟨h₁,h⟩)
    have hr : (16*L-x)/(4*L) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
    rw [sourceCuspRemainderPlateauWeight,Real.smoothTransition.zero_of_nonpos hr,mul_zero]
  · have hl : (x-(T+L)/2)/((L-T)/4) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    rw [sourceCuspRemainderPlateauWeight,Real.smoothTransition.zero_of_nonpos hl,zero_mul]

theorem sourceCuspHeightShellBump_contDiffOn (L : ℝ) :
    ContDiffOn ℝ (∞ : ℕ∞ω) (sourceCuspHeightShellBump L) (Ioi 0) := by
  apply sourceCuspShellBump_contDiff.comp_contDiffOn
  exact (Real.contDiffOn_log.mono (fun _ h => ne_of_gt h)).sub contDiffOn_const

theorem sourceCuspHeightShellBump_sq_support (L : ℝ) (hL : 0 < L) :
    ∀ x : ℝ, x ∉ Icc L (8*L) → 0 < x → (sourceCuspHeightShellBump L x)^2 = 0 := by
  intro x hx hxp
  have hout : x ≤ L ∨ 8*L ≤ x := by
    by_cases h : L ≤ x
    · exact Or.inr (lt_of_not_ge (fun h' => hx ⟨h,h'⟩)).le
    · exact Or.inl (le_of_not_ge h)
  rw [(sourceCuspHeightShell_outside 1 L x hL hxp hout).1]
  norm_num

variable {s : ℂ} (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2*s.re+1)
variable (T L : ℝ) (hT : 1 < T) (hTL : T < L)

def sourceKPCompactRemainderPlateauCore {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (T L : ℝ) (hT : 1 < T) (hTL : T < L) : sourceKPCompactC2Core K hζ :=
  sourceKPCompactHighLocalizedRemainderCore K hζ s T ((T+L)/2) (16*L) hT
    (by linarith) (by linarith [(zero_lt_one.trans hT).trans hTL])
    (sourceCuspRemainderPlateauWeight T L)
    ((sourceCuspRemainderPlateauWeight_contDiff T L).of_le (by simp)).contDiffOn
    (fun x hx _ => sourceCuspRemainderPlateauWeight_zero T L x ((zero_lt_one.trans hT).trans hTL) hTL hx)
    (sourceKPAdelicNonconstantProductChart_contDiffAt_two K hζ hs)


def sourceKPCompactRemainderShellTest {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (T L : ℝ) (hT : 1 < T) (hTL : T < L) : sourceKPCompactC2Core K hζ :=
  sourceKPCompactHighLocalizedRemainderCore K hζ s T L (8*L) hT hTL
    (by linarith [(zero_lt_one.trans hT).trans hTL])
    (fun x => (sourceCuspHeightShellBump L x)^2)
    (((sourceCuspHeightShellBump_contDiffOn L).of_le (by simp)).pow 2)
    (sourceCuspHeightShellBump_sq_support L ((zero_lt_one.trans hT).trans hTL))
    (sourceKPAdelicNonconstantProductChart_contDiffAt_two K hζ hs)

def sourceKPCompactHighShellCutoffCore
    (T L : ℝ) (hT : 1 < T) (hTL : T < L) : sourceKPCompactC2Core K hζ :=
  sourceKPCompactHeightProfileCore K hζ L (8*L) (hT.trans hTL)
    (by linarith [(zero_lt_one.trans hT).trans hTL]) (sourceCuspHeightShellBump L)
    ((sourceCuspHeightShellBump_contDiffOn L).of_le (by simp))
    (fun x hx hxp => sq_eq_zero_iff.mp
      (sourceCuspHeightShellBump_sq_support L ((zero_lt_one.trans hT).trans hTL) x hx hxp))

include hs hT hTL in
theorem sourceKPCompactRemainderShellTest_support :
    tsupport (sourceKPCompactRemainderShellTest K hζ hs T L hT hTL).val ⊆ {y : Y | H y ∈ Icc L (8*L)} :=
  sourceKPCompactHighLocalizedRemainder_support K hζ s T L (8*L) hT hTL
    (by linarith [(zero_lt_one.trans hT).trans hTL]) (fun x => (sourceCuspHeightShellBump L x)^2)
    (sourceCuspHeightShellBump_sq_support L ((zero_lt_one.trans hT).trans hTL))

include hs hT hTL in
theorem sourceKPCompactRemainderShellTest_eq_mul_plateau (y : Y) :
    (sourceKPCompactRemainderShellTest K hζ hs T L hT hTL).val y =
      (sourceCuspHeightShellBump L (H y) : ℂ)^2 * (sourceKPCompactRemainderPlateauCore K hζ hs T L hT hTL).val y := by
  change sourceKPCompactHighLocalizedRemainder K hζ s T hT (fun x => (sourceCuspHeightShellBump L x)^2) y =
    (sourceCuspHeightShellBump L (H y) : ℂ)^2 *
      sourceKPCompactHighLocalizedRemainder K hζ s T hT (sourceCuspRemainderPlateauWeight T L) y
  by_cases h : T < H y
  · let z : SourceKPCompactHighCusp K hζ T := ⟨y,h⟩
    change sourceKPCompactHighLocalizedRemainder K hζ s T hT (fun x => (sourceCuspHeightShellBump L x)^2) z.val =
      (sourceCuspHeightShellBump L (H z.val) : ℂ)^2 *
        sourceKPCompactHighLocalizedRemainder K hζ s T hT (sourceCuspRemainderPlateauWeight T L) z.val
    rw [sourceKPCompactHighLocalizedRemainder_apply,sourceKPCompactHighLocalizedRemainder_apply,Complex.ofReal_pow]
    by_cases hz : H y ∈ Icc L (8*L)
    · have hL : 0 < L := (zero_lt_one.trans hT).trans hTL
      have hz' : H y ∈ Icc ((T+3*L)/4) (12*L) := ⟨by linarith [hz.1],by linarith [hz.2]⟩
      have hweight : sourceCuspRemainderPlateauWeight T L (H z.val) = 1 :=
        sourceCuspRemainderPlateauWeight_one T L (H y) hL hTL hz'
      rw [hweight,Complex.ofReal_one,one_mul]
    · have hzero : (sourceCuspHeightShellBump L (H z.val))^2 = 0 :=
        sourceCuspHeightShellBump_sq_support L ((zero_lt_one.trans hT).trans hTL) (H y) hz
          (sourceKPAutomorphicCompactOrbitHeight_pos K hζ y)
      rw [← Complex.ofReal_pow,hzero,Complex.ofReal_zero,zero_mul,zero_mul]
  · rw [sourceKPCompactHighLocalizedRemainder_zero_of_low K hζ s T hT _ y (le_of_not_gt h),
      sourceKPCompactHighLocalizedRemainder_zero_of_low K hζ s T hT _ y (le_of_not_gt h),mul_zero]

def sourceCuspShellTestCoverWeight (T L x : ℝ) : ℝ :=
  let A := ((T+3*L)/4+L)/2
  Real.smoothTransition ((x-A)/(L-A)) * Real.smoothTransition ((10*L-x)/(2*L))

theorem sourceCuspShellTestCoverWeight_contDiff (T L : ℝ) :
    ContDiff ℝ (∞ : ℕ∞ω) (sourceCuspShellTestCoverWeight T L) :=
  (Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)).mul
    (Real.smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).div_const _))

theorem sourceCuspShellTestCoverWeight_one (T L x : ℝ) (hL : 0 < L) (hTL : T < L)
    (hx : x ∈ Icc L (8*L)) : sourceCuspShellTestCoverWeight T L x = 1 := by
  let A := ((T+3*L)/4+L)/2
  have hlo : 1 ≤ (x-A)/(L-A) := by
    apply (le_div_iff₀ (by dsimp only [A]; linarith)).mpr
    linarith [hx.1]
  have hhi : 1 ≤ (10*L-x)/(2*L) := by
    apply (le_div_iff₀ (by positivity : 0 < 2*L)).mpr
    linarith [hx.2]
  change Real.smoothTransition ((x-A)/(L-A)) * Real.smoothTransition ((10*L-x)/(2*L)) = 1
  rw [Real.smoothTransition.one_of_one_le hlo,Real.smoothTransition.one_of_one_le hhi,one_mul]

theorem sourceCuspShellTestCoverWeight_zero (T L x : ℝ) (hL : 0 < L) (hTL : T < L)
    (hx : x ∉ Icc (((T+3*L)/4+L)/2) (10*L)) : sourceCuspShellTestCoverWeight T L x = 0 := by
  let A := ((T+3*L)/4+L)/2
  change Real.smoothTransition ((x-A)/(L-A)) * Real.smoothTransition ((10*L-x)/(2*L)) = 0
  by_cases hlo : A ≤ x
  · have hhi : 10*L < x := lt_of_not_ge (fun h => hx ⟨hlo,h⟩)
    have hr : (10*L-x)/(2*L) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
    rw [Real.smoothTransition.zero_of_nonpos hr,mul_zero]
  · have hA : 0 ≤ L-A := by dsimp only [A]; linarith
    have hl : (x-A)/(L-A) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hA
    rw [Real.smoothTransition.zero_of_nonpos hl,zero_mul]

def sourceKPCompactShellTestCoverCore
    (T L : ℝ) (hT : 1 < T) (hTL : T < L) : sourceKPCompactC2Core K hζ :=
  sourceKPCompactHeightProfileCore K hζ (((T+3*L)/4+L)/2) (10*L)
    (by linarith) (by linarith [(zero_lt_one.trans hT).trans hTL])
    (sourceCuspShellTestCoverWeight T L)
    ((sourceCuspShellTestCoverWeight_contDiff T L).of_le (by simp)).contDiffOn
    (fun x hx _ => sourceCuspShellTestCoverWeight_zero T L x ((zero_lt_one.trans hT).trans hTL) hTL hx)

include hT hTL in
theorem sourceKPCompactShellTestCoverCore_support :
    tsupport (sourceKPCompactShellTestCoverCore K hζ T L hT hTL).val ⊆
      {y : Y | H y ∈ Ioo ((T+3*L)/4) (12*L)} := by
  let A := ((T+3*L)/4+L)/2
  have hL : 0 < L := (zero_lt_one.trans hT).trans hTL
  have hS := sourceKPAutomorphicCompactHighBand_isCompact K hζ A (10*L) (by dsimp only [A]; linarith)
    (by dsimp only [A]; linarith)
  have hs : tsupport (sourceKPCompactShellTestCoverCore K hζ T L hT hTL).val ⊆ {y : Y | H y ∈ Icc A (10*L)} := by
    apply closure_minimal _ hS.isClosed
    intro y hy
    by_contra hx
    exact hy (Complex.ofReal_eq_zero.mpr (sourceCuspShellTestCoverWeight_zero T L (H y) hL hTL hx))
  intro y hy
  have h := hs hy
  exact ⟨by dsimp only [A] at h; linarith [h.1],by linarith [h.2]⟩

include hT hTL in
theorem sourceKPCompactShellTestCoverCore_one (y : Y) (hy : H y ∈ Icc L (8*L)) :
    (sourceKPCompactShellTestCoverCore K hζ T L hT hTL).val y = 1 := by
  change (sourceCuspShellTestCoverWeight T L (H y) : ℂ) = 1
  rw [sourceCuspShellTestCoverWeight_one T L (H y) ((zero_lt_one.trans hT).trans hTL) hTL hy,Complex.ofReal_one]

end
end ArtinMatthews

/-! The actual square-cutoff test on the compact quotient gives the
Caccioppoli estimate for the high-cusp remainder. -/
namespace ArtinMatthews
open NumberField Matrix Topology Set MeasureTheory Filter SourceHyperbolicGreen OAI.CubicEisenstein
open scoped NumberField MatrixGroups AdeleRing ContDiff
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "P" => ProductSpace (InfinitePlace K)
local notation "U" => productUpper (InfinitePlace K)
local notation "H" => sourceKPAutomorphicCompactOrbitHeight K hζ
local notation "μ" => sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)
local notation "ν" => productVolume (InfinitePlace K)

variable {s : ℂ} (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2*s.re+1)
variable (T L : ℝ) (hT : 1 < T) (hTL : T < L)

local notation "Λ" => ((InfinitePlace.nrComplexPlaces K : ℂ)*(1-4*s^2))
local notation "v" => sourceKPCompactRemainderPlateauCore K hζ hs T L hT hTL
local notation "φ" => sourceKPCompactRemainderShellTest K hζ hs T L hT hTL
local notation "η" => sourceKPCompactHighShellCutoffCore K hζ T L hT hTL
local notation "ηᵣ" => fun y : Y => sourceCuspHeightShellBump L (H y)

include hs hT hTL

theorem sourceKPCompactRemainderShellTest_weak :
    sourceKPCompactDirichletCore K hζ φ v =
      Λ * (∫ y, star ((φ).val y)*(v).val y ∂μ) := by
  let χ := sourceKPCompactShellTestCoverCore K hζ T L hT hTL
  let V : Set Y := {y | H y ∈ Ioo ((T+3*L)/4) (12*L)}
  let F : Y → ℂ := Λ • (v).val
  have hF : Continuous F := (v).prop.1.const_smul Λ
  have hχ : ∀ y ∈ tsupport (φ).val, χ.val y = 1 := fun y hy =>
    sourceKPCompactShellTestCoverCore_one K hζ T L hT hTL y
      (sourceKPCompactRemainderShellTest_support K hζ hs T L hT hTL hy)
  have hχV : tsupport χ.val ⊆ V := sourceKPCompactShellTestCoverCore_support K hζ T L hT hTL
  have hweak (b : SourceKPFiniteLevelFiber K hζ) (ψ : h1Tests (InfinitePlace K) 2)
      (hψ : ∀ x ∈ tsupport ψ.val, x ∈ U ∧
        sourceKPUpperToCompact K hζ b (sourceKPArchEuclideanUpperMap K x) ∈ V) :
      (∫ x, productGradientPair ψ.val (sourceKPCompactChartPullback K hζ (v).val b) x ∂ν) =
        ∫ x, star (ψ.val x)*sourceKPCompactChartPullback K hζ F b x ∂ν := by
    have h := sourceKPCompactHighLocalizedRemainder_weak_native K hζ hs T ((T+3*L)/4) (12*L)
      hT (by linarith) (sourceCuspRemainderPlateauWeight T L)
      (fun x hx => sourceCuspRemainderPlateauWeight_one T L x ((zero_lt_one.trans hT).trans hTL)
        hTL ⟨hx.1.le,hx.2.le⟩) b (((v).prop.2.2 b).of_le (by norm_num)) ψ
      (fun x hx => (hψ x hx).2)
    change (∫ x, productGradientPair ψ.val (sourceKPCompactChartPullback K hζ (v).val b) x ∂ν) =
      Λ * (∫ x, star (ψ.val x)*sourceKPCompactChartPullback K hζ (v).val b x ∂ν) at h
    rw [h,← integral_const_mul]
    dsimp only [F]
    rw [sourceKPCompactChartPullback_smul]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by simp only [Pi.smul_apply,smul_eq_mul]; ring
  rw [sourceKPCompactCore_weak_of_chart_supported K hζ φ v χ F hF V hχ hχV hweak,
    ← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by simp only [F,Pi.smul_apply,smul_eq_mul]; ring

theorem sourceKPCompactRemainderShell_caccioppoli_pointwise (y : Y) :
    (ηᵣ y)^2*sourceKPCompactCoreEnergy K hζ v y ≤
      2*(sourceKPCompactCorePairDensity K hζ φ v y).re +
        4*sourceKPCompactCoreEnergy K hζ η y*‖(v).val y‖^2 := by
  obtain ⟨b,p,rfl⟩ := sourceKPUpperToCompact_cover K hζ y
  let x := sourceKPArchUpperEuclideanMap K p
  have hx : x ∈ U := fun w _ => sourceKPArchUpperEuclidean_positive K p w
  let A := sourceKPCompactChartPullback K hζ (η).val b
  let a : P → ℝ := fun z => (A z).re
  let u := sourceKPCompactChartPullback K hζ (v).val b
  have hA : (fun z => (a z : ℂ)) = A := by
    funext z
    change ((A z).re : ℂ) = A z
    by_cases hz : z ∈ U
    · have hval : A z = (sourceCuspHeightShellBump L (H (sourceKPUpperToCompact K hζ b
          (sourceKPArchEuclideanUpperMap K z))) : ℂ) :=
        sourceKPCompactChartPullback_of_positive K hζ (η).val b z hz
      rw [hval,Complex.ofReal_re]
    · have hzero : A z = 0 := sourceKPCompactChartPullback_of_not_positive K hζ (η).val b z hz
      rw [hzero,Complex.zero_re,Complex.ofReal_zero]
  have hφ : sourceKPCompactChartPullback K hζ (φ).val b = fun z => (a z : ℂ)^2*u z := by
    funext z
    change sourceKPCompactChartPullback K hζ (φ).val b z = (a z : ℂ)^2*u z
    have hae : (a z : ℂ) = A z := congrFun hA z
    by_cases hz : z ∈ U
    · rw [hae]
      simp only [u,A,sourceKPCompactChartPullback_of_positive K hζ (φ).val b z hz,
        sourceKPCompactChartPullback_of_positive K hζ (η).val b z hz,
        sourceKPCompactChartPullback_of_positive K hζ (v).val b z hz]
      exact sourceKPCompactRemainderShellTest_eq_mul_plateau K hζ hs T L hT hTL _
    · rw [hae]
      simp only [u,A,sourceKPCompactChartPullback_of_not_positive K hζ (φ).val b z hz,
        sourceKPCompactChartPullback_of_not_positive K hζ (η).val b z hz,
        sourceKPCompactChartPullback_of_not_positive K hζ (v).val b z hz,mul_zero]
  have hd : DifferentiableAt ℝ a x := Complex.reCLM.differentiableAt.comp x
    ((((η).prop.2.2 b x hx).contDiffAt ((productUpper_isOpen (InfinitePlace K)).mem_nhds hx)).differentiableAt
      (by norm_num))
  have hu : DifferentiableAt ℝ u x :=
    (((v).prop.2.2 b x hx).contDiffAt ((productUpper_isOpen (InfinitePlace K)).mem_nhds hx)).differentiableAt
      (by norm_num)
  have ha : a x = ηᵣ (sourceKPUpperToCompact K hζ b p) := by
    have he := sourceKPCompactChartPullback_of_positive K hζ (η).val b x hx
    rw [show sourceKPArchEuclideanUpperMap K x = p from sourceKPArchUpperEuclideanMap_left_inverse K p] at he
    exact congrArg Complex.re he
  have hv : u x = (v).val (sourceKPUpperToCompact K hζ b p) := by
    simpa only [u,x,sourceKPArchUpperEuclideanMap_left_inverse] using
      sourceKPCompactChartPullback_of_positive K hζ (v).val b x hx
  have he := product_caccioppoli_pointwise hd hu
  rw [hA,← hφ,ha,hv] at he
  rw [sourceKPCompactCoreEnergy_chart,sourceKPCompactCoreEnergy_chart,sourceKPCompactCorePairDensity_chart]
  exact he

theorem sourceKPCompactRemainderShell_caccioppoli :
    (∫ y, (ηᵣ y)^2*sourceKPCompactCoreEnergy K hζ v y ∂μ) ≤
      2*‖Λ‖*(∫ y, (ηᵣ y)^2*‖(v).val y‖^2 ∂μ) +
        4*(∫ y, sourceKPCompactCoreEnergy K hζ η y*‖(v).val y‖^2 ∂μ) := by
  let F : Y → ℝ := fun y => (ηᵣ y)^2*sourceKPCompactCoreEnergy K hζ v y
  let M : Y → ℝ := fun y => (ηᵣ y)^2*‖(v).val y‖^2
  let B : Y → ℝ := fun y => sourceKPCompactCoreEnergy K hζ η y*‖(v).val y‖^2
  let Q := sourceKPCompactCorePairDensity K hζ φ v
  letI := sourceKPAutomorphicCompactHaar_finiteOnCompacts K hζ
  have hη : Continuous ηᵣ := by
    have h := Complex.continuous_re.comp (η).prop.1
    change Continuous (fun y => ((sourceCuspHeightShellBump L (H y) : ℂ)).re) at h
    simpa only [Complex.ofReal_re] using h
  have hFc := (hη.pow 2).mul (sourceKPCompactCoreEnergy_continuous K hζ v)
  have hF : Integrable F μ := hFc.integrable_of_hasCompactSupport
    (sourceKPCompactCoreEnergy_hasCompactSupport K hζ v).mul_left
  have hM : Integrable M μ := ((hη.pow 2).mul ((v).prop.1.norm.pow 2)).integrable_of_hasCompactSupport
    (((v).prop.2.1.comp_left norm_zero).comp_left (zero_pow (by norm_num : (2 : ℕ) ≠ 0))).mul_left
  have hBc := (sourceKPCompactCoreEnergy_continuous K hζ η).mul ((v).prop.1.norm.pow 2)
  have hB : Integrable B μ := hBc.integrable_of_hasCompactSupport
    (sourceKPCompactCoreEnergy_hasCompactSupport K hζ η).mul_right
  have hQ : Integrable Q μ := sourceKPCompactCorePairDensity_integrable K hζ φ v
  have hTest : (∫ y, Q y ∂μ) = Λ * ((∫ y, M y ∂μ : ℝ) : ℂ) := by
    change sourceKPCompactDirichletCore K hζ φ v = _
    rw [sourceKPCompactRemainderShellTest_weak K hζ hs T L hT hTL,
      ← integral_complex_ofReal]
    congr 1
    apply integral_congr_ae
    exact Eventually.of_forall fun y => by
      change star ((φ).val y)*(v).val y = (M y : ℂ)
      rw [sourceKPCompactRemainderShellTest_eq_mul_plateau K hζ hs T L hT hTL y]
      change star ((ηᵣ y : ℂ)^2*(v).val y)*(v).val y = (((ηᵣ y)^2*‖(v).val y‖^2 : ℝ) : ℂ)
      have hv : star ((v).val y)*(v).val y = ((‖(v).val y‖^2 : ℝ) : ℂ) := by
        simpa only [Complex.star_def,Complex.ofReal_pow] using Complex.conj_mul' ((v).val y)
      rw [star_mul,star_pow,show star (ηᵣ y : ℂ) = (ηᵣ y : ℂ) by simp [Complex.star_def]]
      rw [mul_comm (star ((v).val y)),mul_assoc,hv]
      simp only [Complex.ofReal_mul,Complex.ofReal_pow]
  have hP : F ≤ᵐ[μ] fun y => 2*(Q y).re+4*B y :=
    Eventually.of_forall fun y => by
      have h := sourceKPCompactRemainderShell_caccioppoli_pointwise K hζ hs T L hT hTL y
      simpa only [F,Q,B,mul_assoc] using h
  have hPre : Integrable (fun y => (Q y).re) μ := hQ.re
  have hIntRe : (∫ y, (Q y).re ∂μ) = (∫ y, Q y ∂μ).re := integral_re hQ
  have he := integral_mono_ae hF ((hPre.const_mul 2).add (hB.const_mul 4)) hP
  change (∫ y, F y ∂μ) ≤ ∫ y, 2*(Q y).re+4*B y ∂μ at he
  rw [integral_add (hPre.const_mul 2) (hB.const_mul 4),integral_const_mul,integral_const_mul,
    hIntRe,hTest] at he
  have hMp : 0 ≤ ∫ y, M y ∂μ := integral_nonneg (fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hr := mul_le_mul_of_nonneg_right (Complex.re_le_norm Λ) hMp
  have hprod : (Λ * ((∫ y, M y ∂μ : ℝ) : ℂ)).re = Complex.re Λ * (∫ y, M y ∂μ) := by
    rw [Complex.mul_re]
    simp only [Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  rw [hprod] at he
  have hcompare := add_le_add (mul_le_mul_of_nonneg_left hr (by norm_num : (0 : ℝ) ≤ 2))
    (le_rfl : 4*(∫ y, B y ∂μ) ≤ 4*(∫ y, B y ∂μ))
  change (∫ y, F y ∂μ) ≤ 2*‖Λ‖*(∫ y, M y ∂μ)+4*(∫ y, B y ∂μ)
  simpa only [mul_assoc] using he.trans hcompare

end
end ArtinMatthews

/-! Transport the actual compact-quotient square-cutoff estimate to the
framed high-cusp measure, keeping the native height and energy formulas. -/
namespace ArtinMatthews
open NumberField Matrix Topology Set MeasureTheory Filter SourceHyperbolicGreen OAI.CubicEisenstein
open scoped NumberField MatrixGroups AdeleRing ContDiff
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "X" => SourceKPAutomorphicLevel K hζ
local notation "P" => ProductSpace (InfinitePlace K)
local notation "U" => productUpper (InfinitePlace K)
local notation "H" => sourceKPAutomorphicOrbitHeight K hζ
local notation "Hc" => sourceKPAutomorphicCompactOrbitHeight K hζ
local notation "μY" => sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)
local notation "μX" => sourceKPAutomorphicMeasure K hζ (sourceKPArchHaar K hζ)

theorem sourceKPCompact_integral_eq_high_frame (T : ℝ) (F : Y → ℝ) (hF : Measurable F)
    (hzero : ∀ y, Hc y ≤ T → F y = 0) :
    (∫ y, F y ∂μY) = ∫ x : SourceKPHighCuspAutomorphic K hζ T,
      F (sourceKPAutomorphicCompactMk K hζ x.val) ∂sourceKPHighCuspMeasure K hζ T := by
  let m := sourceKPAutomorphicCompactMk K hζ
  let G := F ∘ m
  have hm : Measurable m := sourceKPAutomorphicCompactMk_measurable K hζ
  have hG : Measurable G := hF.comp hm
  calc
    _ = ∫ x, G x ∂μX := integral_map hm.aemeasurable hF.aestronglyMeasurable
    _ = ∫ x in {x | T < H x}, G x ∂μX := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      exact hzero (m x) (le_of_not_gt hx)
    _ = _ := by
      rw [← sourceKPHighCuspMeasure_map_val K hζ T]
      exact integral_map measurable_subtype_coe.aemeasurable hG.aestronglyMeasurable

private theorem sourceKPAdelicProductHeight_native_factor
    (qf : SourceKPFiniteAdeleProjective K hζ) (p : P) (hp : p ∈ U) :
    sourceKPAdelicProductHeight K hζ (1,qf) p =
      sourceKPAdelicCoverHeight K hζ (1,qf) * ∏ w, p w 2^2 := by
  let a := ProjGenLinGroup.mk (sourceArchUpperHalfspaceMatrix K hζ p (fun w => productUpper_pos hp w))
  rw [sourceKPAdelicProductHeight,dif_pos (fun w => productUpper_pos hp w)]
  have hpair : ((1,qf) : SourceKPAdelicProjective K hζ)*(a,1) = (a,qf) :=
    Prod.ext (one_mul _) (mul_one _)
  change sourceKPAdelicCoverHeight K hζ ((1,qf)*(a,1)) = _
  rw [hpair,sourceKPAdelicCoverHeight_native_factor]
  rw [show sourceKPArchNativeCoordinates K hζ a = p from sourceKPArchNativeCoordinates_section K hζ p _]

variable {s : ℂ} (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2*s.re+1)
variable (T L : ℝ) (hT : 1 < T) (hTL : T < L)
local notation "η" => sourceKPCompactHighShellCutoffCore K hζ T L hT hTL
local notation "v" => sourceKPCompactRemainderPlateauCore K hζ hs T L hT hTL
local notation "r" => Fintype.card (InfinitePlace K)

theorem sourceKPCompactHighShell_core_eval (x : SourceKPHighCuspAutomorphic K hζ T) :
    let y := sourceKPAutomorphicCompactMk K hζ x.val
    sourceKPCompactCoreEnergy K hζ η y = sourceCuspHeightShellEnergy r L (H x.val) ∧
    (H x.val ∈ Icc L (8*L) →
      sourceKPCompactCoreEnergy K hζ v y = sourceKPHighCuspNonconstantEnergy K hζ hs T hT x ∧
        (v).val y = sourceKPHighCuspNonconstantEisenstein K hζ s T hT x) := by
  dsimp only
  obtain ⟨z,hz⟩ := sourceKPHighCusp_representative K hζ T x
  obtain ⟨q,hq⟩ := sourceKPFiniteLevelMk_surjective K hζ z.val
  have hqx : sourceKPAutomorphicLevelMk K hζ q = x.val := by
    change (Quotient.mk _ (sourceKPFiniteLevelMk K hζ q) : X) = _
    rw [hq]
    exact congrArg Subtype.val hz
  let u := sourceKPArchGramCoordinates K hζ q.1
  let p := sourceKPArchNativeCoordinates K hζ q.1
  have hp : p ∈ U := sourceKPArchNativeCoordinates_positive K hζ q.1
  let b : SourceKPFiniteLevelFiber K hζ := QuotientGroup.mk q.2
  have hy : sourceKPUpperToCompact K hζ b u = sourceKPAutomorphicCompactMk K hζ x.val :=
    (sourceKPUpperToCompact_mk K hζ b q.1).trans (congrArg (sourceKPAutomorphicCompactMk K hζ) hqx)
  have hH : sourceKPAdelicCoverHeight K hζ q = H x.val := by
    rw [← sourceKPFiniteLevelHeight_mk,hq,← sourceKPHighCuspProjection_orbitHeight K hζ T hT z,hz]
  let C := sourceKPAdelicCoverHeight K hζ (1,q.2)
  have hC : 0 < C := sourceKPAdelicCoverHeight_pos K hζ (1,q.2)
  let G := sourceKPAdelicProductHeight K hζ (1,q.2)
  have hGp : G p = C * ∏ w, p w 2 ^ 2 := sourceKPAdelicProductHeight_native_factor K hζ q.2 p hp
  have hG : G p = H x.val :=
    hGp.trans ((sourceKPAdelicCoverHeight_native_factor K hζ q.1 q.2).symm.trans hH)
  have hhigh : T < G p := hG.symm ▸ x.property
  have hhigh₁ : 1 < sourceKPAdelicProductHeight K hζ
      (sourceKPAdelicProjectiveRationalLift K hζ 1*(1,q.2)) p := by
    simpa only [map_one,one_mul] using hT.trans hhigh
  have hheight := sourceKPUpperToCompact_height_eventuallyEq K hζ q.2 1 p hp hhigh₁
  simp only [map_one,one_mul] at hheight
  have hη : sourceKPCompactChartPullback K hζ (η).val b =ᶠ[𝓝 p]
      fun w => (sourceProductShellCutoff C (Real.log L) w : ℂ) := by
    filter_upwards [(productUpper_isOpen (InfinitePlace K)).mem_nhds hp,hheight] with w hw hheightw
    change Hc (sourceKPUpperToCompact K hζ b (sourceKPArchEuclideanUpperMap K w)) = G w at hheightw
    change sourceKPCompactChartPullback K hζ (η).val b w = _
    rw [sourceKPCompactChartPullback_of_positive K hζ (η).val b w hw]
    change (sourceCuspHeightShellBump L (Hc (sourceKPUpperToCompact K hζ b
      (sourceKPArchEuclideanUpperMap K w))) : ℂ) = _
    have hGw : G w = C * ∏ j, w j 2^2 := sourceKPAdelicProductHeight_native_factor K hζ q.2 w hw
    rw [hheightw,hGw,
      (sourceCuspHeightShell_native K L C hC w hw).1]
  constructor
  · rw [← hy,sourceKPCompactCoreEnergy_chart]
    change productGradientEnergy (sourceKPCompactChartPullback K hζ (η).val b) p = _
    have hE : productGradientEnergy (sourceKPCompactChartPullback K hζ (η).val b) p =
        productGradientEnergy (fun w => (sourceProductShellCutoff C (Real.log L) w : ℂ)) p := by
      simp only [productGradientEnergy,productPartial,hη.fderiv_eq (𝕜 := ℝ)]
    rw [hE,(sourceCuspHeightShell_native K L C hC p hp).2,hGp.symm.trans hG]
  · intro hband
    have hL : 0 < L := (zero_lt_one.trans hT).trans hTL
    let A := (T+3*L)/4
    have hpband : G p ∈ Ioo A (12*L) := by
      rw [hG]
      exact ⟨by dsimp only [A]; linarith [hband.1],by linarith [hband.2]⟩
    have hnear : ∀ᶠ w in 𝓝 p, G w ∈ Ioo A (12*L) :=
      (sourceKPAdelicProductHeight_contDiffAt K hζ (1,q.2) p
        (fun w => productUpper_pos hp w)).continuousAt.eventually (isOpen_Ioo.mem_nhds hpband)
    have hγ : T < sourceKPAdelicProductHeight K hζ
        (sourceKPAdelicProjectiveRationalLift K hζ 1*(1,q.2)) p := by
      simpa only [map_one,one_mul] using hhigh
    have hV := sourceKPCompactHighLocalizedRemainder_chart_eventuallyEq K hζ s T hT
      (sourceCuspRemainderPlateauWeight T L) q.2 1 p hp hγ
    simp only [map_one,one_mul] at hV
    let R := sourceKPAdelicNonconstantProductChart K hζ s (1,q.2)
    have hv : sourceKPCompactChartPullback K hζ (v).val b =ᶠ[𝓝 p] R := by
      filter_upwards [hV,hnear] with w hw hwb
      change sourceKPCompactChartPullback K hζ (v).val b w =
        (sourceCuspRemainderPlateauWeight T L (G w) : ℂ)*R w at hw
      rw [sourceCuspRemainderPlateauWeight_one T L _ hL hTL ⟨hwb.1.le,hwb.2.le⟩,
        Complex.ofReal_one,one_mul] at hw
      exact hw
    have hR : sourceKPHighCuspNonconstantEisenstein K hζ s T hT x =
        sourceKPAdelicNonconstantEisenstein K hζ s q := by
      rw [← hz,sourceKPHighCuspNonconstantEisenstein_rep,← hq,sourceKPFiniteLevelNonconstantEisenstein_mk]
    have hEnergy : sourceKPHighCuspNonconstantEnergy K hζ hs T hT x =
        sourceKPAdelicNonconstantEnergy K hζ s q := by
      rw [← hz]
      exact sourceKPHighCuspNonconstantEnergy_adelic K hζ hs T hT z q hq
    constructor
    · rw [← hy,sourceKPCompactCoreEnergy_chart,hEnergy]
      change productGradientEnergy (sourceKPCompactChartPullback K hζ (v).val b) p = productGradientEnergy R p
      simp only [productGradientEnergy,productPartial,hv.fderiv_eq (𝕜 := ℝ)]
    · rw [hR]
      have he := hv.eq_of_nhds
      change sourceKPCompactChartPullback K hζ (v).val b p = R p at he
      rw [sourceKPCompactChartPullback_of_positive K hζ (v).val b p hp] at he
      change (v).val (sourceKPUpperToCompact K hζ b (sourceKPArchEuclideanUpperMap K
        (sourceKPArchUpperEuclideanMap K u))) = R p at he
      rw [sourceKPArchUpperEuclideanMap_left_inverse,hy] at he
      exact he.trans (sourceKPAdelicNonconstantProductChart_nativeCoordinates K hζ s q)

include hTL in
theorem sourceKPHighShellEnergyEstimate_actual : sourceKPHighShellEnergyEstimate K hζ hs T hT L := by
  let ηᵣ : Y → ℝ := fun y => sourceCuspHeightShellBump L (Hc y)
  let F : Y → ℝ := fun y => (ηᵣ y)^2*sourceKPCompactCoreEnergy K hζ v y
  let M : Y → ℝ := fun y => (ηᵣ y)^2*‖(v).val y‖^2
  let B : Y → ℝ := fun y => sourceKPCompactCoreEnergy K hζ η y*‖(v).val y‖^2
  have hη : Continuous ηᵣ := by
    have h := Complex.continuous_re.comp (η).prop.1
    change Continuous (fun y => ((sourceCuspHeightShellBump L (Hc y) : ℂ)).re) at h
    simpa only [Complex.ofReal_re] using h
  have hF : Continuous F := (hη.pow 2).mul (sourceKPCompactCoreEnergy_continuous K hζ v)
  have hM : Continuous M := (hη.pow 2).mul ((v).prop.1.norm.pow 2)
  have hB : Continuous B := (sourceKPCompactCoreEnergy_continuous K hζ η).mul ((v).prop.1.norm.pow 2)
  have hL : 0 < L := (zero_lt_one.trans hT).trans hTL
  have hSupp : tsupport (η).val ⊆ {y : Y | Hc y ∈ Icc L (8*L)} := by
    have hc := sourceKPAutomorphicCompactHighBand_isCompact K hζ L (8*L) (hT.trans hTL) (by linarith)
    apply closure_minimal _ hc.isClosed
    intro y hy
    by_contra hnot
    exact hy (Complex.ofReal_eq_zero.mpr (sq_eq_zero_iff.mp
      (sourceCuspHeightShellBump_sq_support L hL (Hc y) hnot
        (sourceKPAutomorphicCompactOrbitHeight_pos K hζ y))))
  have hzero (y : Y) (hy : Hc y ≤ T) :
      F y = 0 ∧ M y = 0 ∧ B y = 0 := by
    have hηz : ηᵣ y = 0 := (sourceCuspHeightShell_outside r L (Hc y) hL
      (sourceKPAutomorphicCompactOrbitHeight_pos K hζ y) (Or.inl (hy.trans hTL.le))).1
    have hηE : sourceKPCompactCoreEnergy K hζ η y = 0 :=
      sourceKPCompactCoreEnergy_zero_outside K hζ η (fun h => (not_le_of_gt hTL) ((hSupp h).1.trans hy))
    simp only [F,M,B,hηz,hηE,zero_pow (by norm_num : (2 : ℕ) ≠ 0),zero_mul,and_self]
  have h := sourceKPCompactRemainderShell_caccioppoli K hζ hs T L hT hTL
  change (∫ y, F y ∂μY) ≤ _ * (∫ y, M y ∂μY) + 4*(∫ y, B y ∂μY) at h
  rw [sourceKPCompact_integral_eq_high_frame K hζ T F hF.measurable (fun y hy => (hzero y hy).1),
    sourceKPCompact_integral_eq_high_frame K hζ T M hM.measurable (fun y hy => (hzero y hy).2.1),
    sourceKPCompact_integral_eq_high_frame K hζ T B hB.measurable (fun y hy => (hzero y hy).2.2)] at h
  let R := sourceKPHighCuspNonconstantEisenstein K hζ s T hT
  let E := sourceKPHighCuspNonconstantEnergy K hζ hs T hT
  let m := sourceKPAutomorphicCompactMk K hζ
  have heq (x : SourceKPHighCuspAutomorphic K hζ T) :
      F (m x.val) = (sourceCuspHeightShellBump L (H x.val))^2 * E x ∧
      M (m x.val) = (sourceCuspHeightShellBump L (H x.val))^2 * ‖R x‖^2 ∧
      B (m x.val) = sourceCuspHeightShellEnergy r L (H x.val) * ‖R x‖^2 := by
    have hev := sourceKPCompactHighShell_core_eval K hζ hs T L hT hTL x
    dsimp only [F,M,B,ηᵣ,m,sourceKPAutomorphicCompactOrbitHeight_mk]
    by_cases hband : H x.val ∈ Icc L (8*L)
    · obtain ⟨hE,hR⟩ := hev.2 hband
      rw [hev.1,hE,hR]
      exact ⟨rfl,rfl,rfl⟩
    · have hout : H x.val ≤ L ∨ 8*L ≤ H x.val := by
        by_cases hlo : L ≤ H x.val
        · exact Or.inr (lt_of_not_ge (fun hh => hband ⟨hlo,hh⟩)).le
        · exact Or.inl (le_of_not_ge hlo)
      obtain ⟨hz,hEz⟩ := sourceCuspHeightShell_outside r L (H x.val) hL
        ((zero_lt_one.trans hT).trans x.property) hout
      simp only [hev.1,hz,hEz,zero_pow (by norm_num : (2 : ℕ) ≠ 0),zero_mul,and_self]
  let μ := sourceKPHighCuspMeasure K hζ T
  have hFi : (∫ x, F (m x.val) ∂μ) = ∫ x, (sourceCuspHeightShellBump L (H x.val))^2*E x ∂μ :=
    integral_congr_ae (Eventually.of_forall fun x => (heq x).1)
  have hMi : (∫ x, M (m x.val) ∂μ) = ∫ x, (sourceCuspHeightShellBump L (H x.val))^2*‖R x‖^2 ∂μ :=
    integral_congr_ae (Eventually.of_forall fun x => (heq x).2.1)
  have hBi : (∫ x, B (m x.val) ∂μ) = ∫ x, sourceCuspHeightShellEnergy r L (H x.val)*‖R x‖^2 ∂μ :=
    integral_congr_ae (Eventually.of_forall fun x => (heq x).2.2)
  change (∫ x, F (m x.val) ∂μ) ≤ _*(∫ x, M (m x.val) ∂μ)+4*(∫ x, B (m x.val) ∂μ) at h
  rw [hFi,hMi,hBi] at h
  exact h

end
end ArtinMatthews

/-! Initial-region square integrability of the original Eisenstein
series minus the original incoming cutoff. -/
namespace ArtinMatthews
open NumberField Matrix MeasureTheory Set Topology Filter
open scoped NumberField MatrixGroups AdeleRing ENNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
local notation "X" => SourceKPAutomorphicLevel K hζ
local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "H" => sourceKPAutomorphicOrbitHeight K hζ
local notation "μX" => sourceKPAutomorphicMeasure K hζ (sourceKPArchHaar K hζ)
local notation "μY" => sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)

theorem sourceKPHighRemainderExtension_memLp_actual {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (T A : ℝ) (hT : 1 < T) (hT₂ : 2 ≤ T) (hTA : T < A) :
    MemLp (sourceKPHighRemainderExtension K hζ s T hT) 2
      (Measure.restrict μX {x | A < H x}) := by
  apply sourceKPHighRemainderExtension_memLp_of_shell_energy K hζ hs T hT hT₂ A hTA
  intro n
  have hA : 0 < A := (zero_lt_one.trans hT).trans hTA
  have hAn : A ≤ A*(2 : ℝ)^n := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := n)) hA.le
  exact sourceKPHighShellEnergyEstimate_actual K hζ hs T (A*2^n) hT (hTA.trans_le hAn)

private theorem sourceKPInitialTruncation_high_remainder {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2*s.re+1) (T₀ : ℝ) :
    ∃ A : ℝ, 2 < A ∧ 2*T₀ ≤ A ∧
      MemLp (sourceKPHighRemainderExtension K hζ s 2 one_lt_two) 2
        (Measure.restrict μX {x | A < H x}) := by
  let A : ℝ := max 4 (2*T₀)
  have h2A : (2 : ℝ) < A := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  exact ⟨A,h2A,le_max_right _ _,
    sourceKPHighRemainderExtension_memLp_actual K hζ hs 2 A one_lt_two le_rfl h2A⟩

theorem sourceKPAutomorphicInitialDifference_memLp {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (T₀ : ℝ) (hT₀ : 1 ≤ T₀) :
    MemLp (fun x : X => sourceKPAutomorphicEisenstein K hζ s x -
      sourceKPAutomorphicCutoffEisenstein K hζ T₀ s x) 2 μX := by
  obtain ⟨A,h2A,hcut,hR⟩ := sourceKPInitialTruncation_high_remainder K hζ hs T₀
  exact sourceKPAutomorphicInitialDifference_memLp_of_high_remainder K hζ hs T₀ hT₀ 2 A
    one_lt_two (one_lt_two.trans h2A) h2A.le hcut hR

theorem sourceKPAutomorphicCompactTruncatedEisenstein_memLp {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (T₀ : ℝ) (hT₀ : 1 ≤ T₀) :
    MemLp (sourceKPAutomorphicCompactTruncatedEisenstein K hζ T₀ s) 2 μY := by
  obtain ⟨A,h2A,hcut,hR⟩ := sourceKPInitialTruncation_high_remainder K hζ hs T₀
  exact sourceKPAutomorphicCompactTruncatedEisenstein_memLp_of_high_remainder K hζ hs T₀ hT₀ 2 A
    one_lt_two (one_lt_two.trans h2A) h2A.le hcut hR

def sourceKPAutomorphicCompactInitialTruncatedL2 {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (T₀ : ℝ) (hT₀ : 1 ≤ T₀) : SourceKPAutomorphicL2 K hζ (sourceKPArchHaar K hζ) :=
  (sourceKPAutomorphicCompactTruncatedEisenstein_memLp K hζ hs T₀ hT₀).toLp
    (sourceKPAutomorphicCompactTruncatedEisenstein K hζ T₀ s)

theorem sourceKPAutomorphicCompactInitialTruncatedL2_coe {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (T₀ : ℝ) (hT₀ : 1 ≤ T₀) :
    (sourceKPAutomorphicCompactInitialTruncatedL2 K hζ hs T₀ hT₀ : Y → ℂ) =ᵐ[μY]
      sourceKPAutomorphicCompactTruncatedEisenstein K hζ T₀ s :=
  (sourceKPAutomorphicCompactTruncatedEisenstein_memLp K hζ hs T₀ hT₀).coeFn_toLp

end
end ArtinMatthews
