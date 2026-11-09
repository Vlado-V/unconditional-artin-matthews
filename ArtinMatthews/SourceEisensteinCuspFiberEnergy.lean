module

public import ArtinMatthews.SourceEisensteinCuspEnergyGeometry
public import ArtinMatthews.SourceEisensteinCuspAnisotropic
public import ArtinMatthews.SourceKPCuspUpperAction


set_option backward.privateInPublic true
@[expose] public section

/-! The actual trace-normalized unipotent averages of the remainder's
mass and gradient energy satisfy the anisotropic cusp inequality. -/
namespace ArtinMatthews
open NumberField Matrix MeasureTheory Topology Set Filter OAI.CubicEisenstein SourceHyperbolicGreen
open OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanCharacterLattice.Construction
open scoped NumberField MatrixGroups AdeleRing Classical ContDiff BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
local notation "E" => mixedEmbedding.mixedSpace K
local notation "P" => ProductSpace (InfinitePlace K)
local notation "X" => SourceKPAutomorphicLevel K hζ
local instance sourceCuspFiberAdelicMeasurable : MeasurableSpace 𝔸[K] := borel _
local instance sourceCuspFiberAdelicBorel : BorelSpace 𝔸[K] := ⟨rfl⟩
local notation "ν" => sourceKPAdelicTraceProduct K
local notation "A₀" => sourceKPAdelicFundamentalDomain K

variable (qf : SourceKPFiniteAdeleProjective K hζ)
local notation "d" => sourceKPFixedFiniteCuspPeriod K hζ qf
local notation "Q" => SourceKPCuspPrincipalQuotient K d
local instance sourceCuspFiberQuotientMeasurable : MeasurableSpace Q := borel _
local instance sourceCuspFiberQuotientBorel : BorelSpace Q := ⟨rfl⟩

variable (T : ℝ) (x : SourceKPHighCuspFinite K hζ T)
variable (hqf : (QuotientGroup.mk qf : SourceKPFiniteLevelFiber K hζ) = x.val.2)
include hqf

private theorem sourceCuspFiber_mk : sourceKPFiniteLevelMk K hζ (x.val.1,qf) = x.val :=
  Prod.ext rfl hqf

private theorem sourceCuspFiber_upper_mk (y : 𝔸[K]) :
    sourceKPFiniteLevelMk K hζ (sourceKPAdelicUpperLift K hζ y*(x.val.1,qf)) =
      (Multiplicative.ofAdd y • x).val := by
  rw [sourceKPCuspHighUpper_val,sourceKPFiniteLevelMk_mul,sourceCuspFiber_mk K hζ qf T x hqf]

private theorem sourceCuspFiber_projection_val (y : 𝔸[K]) :
    sourceKPFixedFiniteCuspCover K hζ qf x.val.1 (QuotientAddGroup.mk y) =
      (sourceKPHighCuspProjection K hζ T (Multiplicative.ofAdd y • x)).val :=
  congrArg (fun u : SourceKPFiniteLevelSpace K hζ => (Quotient.mk _ u : X))
    (sourceCuspFiber_upper_mk K hζ qf T x hqf y)

omit hqf in
def sourceKPFixedFiniteCuspHighCover (b : SourceKPFiniteAdeleProjective K hζ)
    (U : ℝ) (z : SourceKPHighCuspFinite K hζ U)
    (hb : (QuotientGroup.mk b : SourceKPFiniteLevelFiber K hζ) = z.val.2) :
    C(SourceKPCuspPrincipalQuotient K (sourceKPFixedFiniteCuspPeriod K hζ b),
      SourceKPHighCuspAutomorphic K hζ U) := by
  let f := sourceKPFixedFiniteCuspCover K hζ b z.val.1
  have hf (u : SourceKPCuspPrincipalQuotient K (sourceKPFixedFiniteCuspPeriod K hζ b)) :
      U < sourceKPAutomorphicOrbitHeight K hζ (f u) := by
    obtain ⟨y,rfl⟩ := QuotientAddGroup.mk_surjective u
    change U < sourceKPAutomorphicOrbitHeight K hζ
      (sourceKPFixedFiniteCuspCover K hζ b z.val.1 (QuotientAddGroup.mk y))
    rw [sourceCuspFiber_projection_val K hζ b U z hb y]
    exact (sourceKPHighCuspProjection K hζ U (Multiplicative.ofAdd y • z)).property
  exact ⟨fun u => ⟨f u,hf u⟩,f.continuous.subtype_mk _⟩

theorem sourceKPFixedFiniteCuspHighCover_mk (y : 𝔸[K]) :
    sourceKPFixedFiniteCuspHighCover K hζ qf T x hqf (QuotientAddGroup.mk y) =
      sourceKPHighCuspProjection K hζ T (Multiplicative.ofAdd y • x) :=
  Subtype.ext (sourceCuspFiber_projection_val K hζ qf T x hqf y)

theorem sourceKPHighCuspNonconstant_upper_eval (s : ℂ) (hT : 1 < T) (y : 𝔸[K]) :
    sourceKPHighCuspNonconstantEisenstein K hζ s T hT
      (sourceKPHighCuspProjection K hζ T (Multiplicative.ofAdd y • x)) =
        sourceKPAdelicNonconstantEisenstein K hζ s (sourceKPAdelicUpperLift K hζ y*(x.val.1,qf)) := by
  rw [sourceKPHighCuspNonconstantEisenstein_rep,← sourceCuspFiber_upper_mk K hζ qf T x hqf y,
    sourceKPFiniteLevelNonconstantEisenstein_mk]

theorem sourceKPHighCuspEnergy_upper_eval {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (hT : 1 < T) (y : 𝔸[K]) :
    sourceKPHighCuspNonconstantEnergy K hζ hs T hT
      (sourceKPHighCuspProjection K hζ T (Multiplicative.ofAdd y • x)) =
        sourceKPAdelicNonconstantEnergy K hζ s (sourceKPAdelicUpperLift K hζ y*(x.val.1,qf)) :=
  sourceKPHighCuspNonconstantEnergy_adelic K hζ hs T hT _ _
    (sourceCuspFiber_upper_mk K hζ qf T x hqf y)

omit hqf in
private theorem sourceCuspFiber_integral_finiteSum {ι : Type*} [Fintype ι]
    {Ω : Type*} [TopologicalSpace Ω] [CompactSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (w : ι → ℝ) (f : ι → Fin 2 → C(Ω,ℂ)) :
    (∫ z, ∑ v, w v * ∑ j, ‖f v j z‖ ^ 2 ∂μ) =
      ∑ v, w v * ∑ j, ∫ z, ‖f v j z‖ ^ 2 ∂μ := by
  have hc (v : ι) (j : Fin 2) : Continuous (fun z => ‖f v j z‖ ^ 2) := (f v j).continuous.norm.pow 2
  have hi (v : ι) (j : Fin 2) : Integrable (fun z => ‖f v j z‖ ^ 2) μ :=
    (hc v j).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [integral_finsetSum _ (fun v _ => (integrable_finsetSum _ (fun j _ => hi v j)).const_mul (w v))]
  apply Finset.sum_congr rfl
  intro v _
  rw [integral_const_mul,integral_finsetSum _ (fun j _ => hi v j)]

theorem sourceKPHighCusp_trace_anisotropic {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (hT : 1 < T) :
    let δ := sourceKPCuspHeightGapExponent K
    let C := sourceKPFiniteLevelHeight K hζ (1,x.val.2)
    let M := fun y : 𝔸[K] => ‖sourceKPHighCuspNonconstantEisenstein K hζ s T hT
      (sourceKPHighCuspProjection K hζ T (Multiplicative.ofAdd y • x))‖ ^ 2
    let W := fun y : 𝔸[K] => sourceKPHighCuspNonconstantEnergy K hζ hs T hT
      (sourceKPHighCuspProjection K hζ T (Multiplicative.ofAdd y • x))
    IntegrableOn M A₀ ν ∧ IntegrableOn W A₀ ν ∧
      (sourceKPCuspHorizontalGapConstant K d / C^δ) *
        (sourceKPFiniteLevelHeight K hζ x.val)^δ * (∫ y in A₀, M y ∂ν) ≤
          ∫ y in A₀, W y ∂ν := by
  dsimp only
  let δ := sourceKPCuspHeightGapExponent K
  let C := sourceKPFiniteLevelHeight K hζ (1,x.val.2)
  let H := sourceKPFiniteLevelHeight K hζ x.val
  let p := sourceKPArchNativeCoordinates K hζ x.val.1
  have hp : ∀ v, 0 < p v 2 := fun v =>
    productUpper_pos (sourceKPArchNativeCoordinates_positive K hζ x.val.1) v
  let a := ProjGenLinGroup.mk (sourceArchUpperHalfspaceMatrix K hζ p hp)
  let f := sourceKPFixedFiniteCuspNonconstantContinuous K hζ qf hs a
  let F := sourceKPFixedFiniteCuspHighCover K hζ qf T x hqf
  let W := sourceKPHighCuspNonconstantEnergy K hζ hs T hT ∘ F
  let M := fun z => ‖f z‖ ^ 2
  have hd : d ≠ 0 := sourceKPFixedFiniteCuspPeriod_ne_zero K hζ qf
  letI := sourceKPCuspPrincipalQuotient_compact K d hd
  letI := sourceKPCuspTraceHaar_probability K d hζ
  letI := source_isTotallyComplex K hζ
  let σ := sourceKPCuspTraceHaar K d
  obtain ⟨g,_hg,hphysical,hP⟩ := sourceKPFixedFiniteCuspNonconstant_native_anisotropic K hζ qf p hp hs
  let D := sourceKPCuspPhysicalDerivativeC K d hζ hd g
  let e := fun z : Q => ∑ v, p v 2 ^ 2 * ∑ j : Fin 2, ‖D v j z‖ ^ 2
  have hM (z : Q) : sourceKPHighCuspNonconstantEisenstein K hζ s T hT (F z) = f z := by
    obtain ⟨v,rfl⟩ := sourceKPCuspArchQuotientMap_surjective K d hd z
    change sourceKPHighCuspNonconstantEisenstein K hζ s T hT
      (F (QuotientAddGroup.mk (mixedAdelicAdd K v))) = _
    rw [sourceKPFixedFiniteCuspHighCover_mk,sourceKPHighCuspNonconstant_upper_eval K hζ qf T x hqf s hT,
      sourceKPAdelicNonconstantEisenstein_upper_mixed_native]
    exact (sourceKPFixedFiniteCuspNonconstant_native_pullback K hζ qf p hp s v).symm
  have he (z : Q) : e z ≤ W z := by
    obtain ⟨v,rfl⟩ := sourceKPCuspArchQuotientMap_surjective K d hd z
    have hw : W (sourceKPCuspArchQuotientMap K d v) =
        productGradientEnergy (sourceKPAdelicNonconstantProductChart K hζ s (1,qf))
          (sourceKPCuspNativePoint K hζ p v) := by
      change sourceKPHighCuspNonconstantEnergy K hζ hs T hT
        (F (QuotientAddGroup.mk (mixedAdelicAdd K v))) = _
      rw [sourceKPFixedFiniteCuspHighCover_mk,
        sourceKPHighCuspEnergy_upper_eval K hζ qf T x hqf hs hT,sourceKPAdelicNonconstantEnergy_upper_mixed]
    rw [hw]
    dsimp only [e,D]
    unfold productGradientEnergy
    apply Finset.sum_le_sum
    intro w _
    rw [sourceKPCuspNativePoint_height]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    rw [Fin.sum_univ_castSucc (fun j : Fin 3 =>
      ‖productPartial (sourceKPAdelicNonconstantProductChart K hζ s (1,qf)) w j
        (sourceKPCuspNativePoint K hζ p v)‖ ^ 2)]
    simp_rw [hphysical v w]
    exact le_add_of_nonneg_right (sq_nonneg _)
  have hmc : Continuous M := f.continuous.norm.pow 2
  have hwc : Continuous W := (sourceKPHighCuspNonconstantEnergy_continuous K hζ hs T hT).comp F.continuous
  have hec : Continuous e := by
    apply continuous_finsetSum
    intro v _
    apply Continuous.const_mul
    apply continuous_finsetSum
    intro j _
    exact (D v j).continuous.norm.pow 2
  have hmi : Integrable M σ := hmc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hwi : Integrable W σ := hwc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hei : Integrable e σ := hec.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hI : (∫ z, e z ∂σ) = ∑ v, p v 2 ^ 2 * ∑ j, ∫ z, ‖D v j z‖ ^ 2 ∂σ :=
    sourceCuspFiber_integral_finiteSum σ (fun v => p v 2 ^ 2) D
  let m : 𝔸[K] → Q := QuotientAddGroup.mk
  have hm : Measurable m := QuotientAddGroup.continuous_mk.measurable
  have hmp : MeasurePreserving m ((ν).restrict A₀) σ := ⟨hm,rfl⟩
  have hmfun (y : 𝔸[K]) :
      ‖sourceKPHighCuspNonconstantEisenstein K hζ s T hT
        (sourceKPHighCuspProjection K hζ T (Multiplicative.ofAdd y • x))‖ ^ 2 = M (m y) := by
    rw [← sourceKPFixedFiniteCuspHighCover_mk K hζ qf T x hqf y]
    exact congrArg (fun u : ℂ => ‖u‖^2) (hM (m y))
  have hwfun (y : 𝔸[K]) : sourceKPHighCuspNonconstantEnergy K hζ hs T hT
      (sourceKPHighCuspProjection K hζ T (Multiplicative.ofAdd y • x)) = W (m y) := by
    rw [← sourceKPFixedFiniteCuspHighCover_mk K hζ qf T x hqf y]
    rfl
  simp_rw [hmfun,hwfun]
  refine ⟨hmp.integrable_comp_of_integrable hmi,hmp.integrable_comp_of_integrable hwi,?_⟩
  have hmI : (∫ y in A₀, M (m y) ∂ν) = ∫ z, M z ∂σ :=
    (integral_map hm.aemeasurable hmi.aestronglyMeasurable).symm
  have hwI : (∫ y in A₀, W (m y) ∂ν) = ∫ z, W z ∂σ :=
    (integral_map hm.aemeasurable hwi.aestronglyMeasurable).symm
  have hH : H = C * ∏ v, p v 2 ^ 2 := by
    change sourceKPFiniteLevelHeight K hζ x.val = C * _
    rw [← sourceCuspFiber_mk K hζ qf T x hqf,sourceKPFiniteLevelHeight_mk,
      sourceKPAdelicCoverHeight_native_factor]
    change sourceKPAdelicCoverHeight K hζ (1,qf)*_ = C*_
    have hC : sourceKPAdelicCoverHeight K hζ (1,qf) = C := by
      change sourceKPFiniteLevelHeight K hζ (1,QuotientGroup.mk qf) = _
      rw [hqf]
    rw [hC]
  have hC : 0 < C := sourceKPFiniteLevelHeight_pos K hζ _
  have hpow : 0 < C^δ := Real.rpow_pos_of_pos hC δ
  have hcoeff : (sourceKPCuspHorizontalGapConstant K d / C^δ) * H^δ =
      sourceKPCuspHorizontalGapConstant K d * (∏ v, p v 2 ^ 2)^δ := by
    rw [hH,Real.mul_rpow hC.le (Finset.prod_nonneg (fun _ _ => sq_nonneg _))]
    field_simp [hpow.ne']
  change (sourceKPCuspHorizontalGapConstant K d / C^δ) * H^δ * _ ≤ _
  rw [hmI,hwI,hcoeff]
  exact (hP.trans_eq hI.symm).trans (integral_mono hei hwi he)

end
end ArtinMatthews
