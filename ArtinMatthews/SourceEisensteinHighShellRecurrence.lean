module

public import ArtinMatthews.SourceEisensteinCuspEnergyGeometry
public import ArtinMatthews.L2DyadicOpenShells
public import ArtinMatthews.SourceCuspShellGradient
public import ArtinMatthews.SourceEisensteinHighEnergy
public import ArtinMatthews.SourceEisensteinHighRemainderContinuity
public import ArtinMatthews.SourceKPCuspUpperAction
public import ArtinMatthews.SourceKPHighCuspMeasure
public import ArtinMatthews.SourceAdelicSecondCountable
public import ArtinMatthews.SourceCuspShellGeometry
public import ArtinMatthews.SourceEisensteinCuspFiberEnergy
public import ArtinMatthews.SourceEisensteinDyadicShellVolume
public import ArtinMatthews.SourceEisensteinHighBand
public import ArtinMatthews.SourceEisensteinHighRemainderMass
public import ArtinMatthews.SourceKPAutomorphicComponentTopology
public import ArtinMatthews.SourceKPCuspFixedFiberSection
public import ArtinMatthews.SourceKPCuspTraceAverage
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual height-shell cutoff and its gradient energy on the full
product of native upper-half-space coordinates. -/
namespace ArtinMatthews
open NumberField Matrix MeasureTheory Topology Set SourceHyperbolicGreen OAI.CubicEisenstein
open scoped NumberField MatrixGroups AdeleRing ContDiff
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceCuspHeightShellBump (L H : ℝ) : ℝ :=
  sourceCuspShellBump (Real.log H-Real.log L)

def sourceCuspHeightShellEnergy (r : ℕ) (L H : ℝ) : ℝ :=
  4*r * (deriv sourceCuspShellBump (Real.log H-Real.log L))^2

theorem sourceCuspHeightShellBump_nonneg (L H : ℝ) : 0 ≤ sourceCuspHeightShellBump L H :=
  sourceCuspShellBump_nonneg _

theorem sourceCuspHeightShellBump_le_one (L H : ℝ) : sourceCuspHeightShellBump L H ≤ 1 :=
  sourceCuspShellBump_le_one _

theorem sourceCuspHeightShellEnergy_nonneg (r : ℕ) (L H : ℝ) :
    0 ≤ sourceCuspHeightShellEnergy r L H := by unfold sourceCuspHeightShellEnergy; positivity

private theorem log_two_pow_mul (L : ℝ) (hL : 0 < L) (n : ℕ) :
    Real.log ((2 : ℝ)^n * L) = (n : ℝ)*Real.log 2 + Real.log L := by
  rw [Real.log_mul (pow_ne_zero n (by norm_num)) hL.ne',Real.log_pow]

theorem sourceCuspHeightShellBump_middle (L H : ℝ) (hL : 0 < L)
    (hlo : 2*L ≤ H) (hhi : H ≤ 4*L) :
    sourceCuspHeightShellBump L H = 1 := by
  have hH : 0 < H := lt_of_lt_of_le (mul_pos (by norm_num) hL) hlo
  have h₁ := Real.log_le_log (by positivity : 0 < (2 : ℝ)*L) hlo
  have h₂ := Real.log_le_log hH hhi
  have he₁ := log_two_pow_mul L hL 1
  have he₂ := log_two_pow_mul L hL 2
  norm_num at he₁ he₂
  rw [he₁] at h₁
  rw [he₂] at h₂
  exact sourceCuspShellBump_one (by linarith) (by linarith)

theorem sourceCuspHeightShell_outside (r : ℕ) (L H : ℝ) (hL : 0 < L) (hH : 0 < H)
    (hout : H ≤ L ∨ 8*L ≤ H) :
    sourceCuspHeightShellBump L H = 0 ∧ sourceCuspHeightShellEnergy r L H = 0 := by
  have hlog : Real.log H-Real.log L ≤ 0 ∨ 3*Real.log 2 ≤ Real.log H-Real.log L := by
    rcases hout with h | h
    · exact Or.inl (sub_nonpos.mpr (Real.log_le_log hH h))
    · have hh := Real.log_le_log (by positivity : 0 < (8 : ℝ)*L) h
      have he := log_two_pow_mul L hL 3
      norm_num at he
      rw [he] at hh
      exact Or.inr (by linarith)
  refine ⟨hlog.elim sourceCuspShellBump_zero_left sourceCuspShellBump_zero_right,?_⟩
  unfold sourceCuspHeightShellEnergy
  rw [sourceCuspShellBump_deriv_zero hlog]
  ring

theorem sourceCuspHeightShellEnergy_uniform_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ L H : ℝ,
      sourceCuspHeightShellEnergy (Fintype.card (InfinitePlace K)) L H ≤ C := by
  obtain ⟨B,hB,hbound⟩ := sourceCuspShellBump_deriv_bound
  refine ⟨4*(Fintype.card (InfinitePlace K) : ℝ)*B^2,by positivity,?_⟩
  intro L H
  unfold sourceCuspHeightShellEnergy
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hn := hbound (Real.log H-Real.log L)
  rw [Real.norm_eq_abs] at hn
  rw [← sq_abs (deriv sourceCuspShellBump (Real.log H-Real.log L))]
  exact pow_le_pow_left₀ (abs_nonneg _) hn 2

theorem sourceCuspHeightShellBump_continuousOn (L : ℝ) :
    ContinuousOn (sourceCuspHeightShellBump L) (Ioi 0) :=
  sourceCuspShellBump_contDiff.continuous.comp_continuousOn
    (Real.continuousOn_log.mono (fun _ hx => ne_of_gt hx) |>.sub continuousOn_const)

theorem sourceCuspHeightShellEnergy_continuousOn (r : ℕ) (L : ℝ) :
    ContinuousOn (sourceCuspHeightShellEnergy r L) (Ioi 0) := by
  unfold sourceCuspHeightShellEnergy
  exact ((sourceCuspShellBump_contDiff.continuous_deriv (by norm_num)).comp_continuousOn
    (Real.continuousOn_log.mono (fun _ hx => ne_of_gt hx) |>.sub continuousOn_const)).pow 2 |>.const_mul _

theorem sourceCuspHeightShell_native (L C : ℝ) (hC : 0 < C)
    (p : ProductSpace (InfinitePlace K)) (hp : p ∈ productUpper (InfinitePlace K)) :
    let H := C*∏ v, p v 2^2
    sourceProductShellCutoff C (Real.log L) p = sourceCuspHeightShellBump L H ∧
    productGradientEnergy (fun q => (sourceProductShellCutoff C (Real.log L) q : ℂ)) p =
      sourceCuspHeightShellEnergy (Fintype.card (InfinitePlace K)) L H := by
  dsimp only
  constructor
  · rw [sourceProductShellCutoff,sourceProductLogHeight_eq C hC p hp,sourceCuspHeightShellBump]
  · rw [sourceProductShellCutoff_energy C (Real.log L) p hp,
      sourceProductLogHeight_eq C hC p hp,sourceCuspHeightShellEnergy]

variable (T L : ℝ) (hT : 1 < T) (hTL : T < L)
local notation "Y" => SourceKPHighCuspAutomorphic K hζ T
local notation "H" => fun q : Y => sourceKPAutomorphicOrbitHeight K hζ (Subtype.val q)
local notation "η" => fun q : Y => sourceCuspHeightShellBump L (H q)
local notation "J" => fun q : Y => sourceCuspHeightShellEnergy (Fintype.card (InfinitePlace K)) L (H q)
local notation "μ" => sourceKPHighCuspMeasure K hζ T

include hTL in
theorem sourceKPHighShell_integrability {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2*s.re+1) :
    let R := sourceKPHighCuspNonconstantEisenstein K hζ s T hT
    let W := sourceKPHighCuspNonconstantEnergy K hζ hs T hT
    Integrable (fun q => (η q)^2*W q) μ ∧
    Integrable (fun q => (η q)^2*‖R q‖^2) μ ∧
    Integrable (fun q => J q*‖R q‖^2) μ ∧
    IntegrableOn (fun q => ‖R q‖^2) {q | H q ∈ Ioc (2*L) (4*L)} μ := by
  dsimp only
  let R := sourceKPHighCuspNonconstantEisenstein K hζ s T hT
  let W := sourceKPHighCuspNonconstantEnergy K hζ hs T hT
  let S : Set Y := {q | H q ∈ Icc L (8*L)}
  have hL : 0 < L := (zero_lt_one.trans hT).trans hTL
  have hH (q : Y) : 0 < H q := (zero_lt_one.trans hT).trans q.property
  letI := sourceKPHighCuspMeasure_finiteOnCompacts K hζ T
  have hS : IsCompact S := sourceKPHighCuspBand_isCompact K hζ T L (8*L) hT hTL (by linarith)
  have hη : Continuous η := (sourceCuspHeightShellBump_continuousOn L).comp_continuous
    (sourceKPHighCuspHeight_continuous K hζ T hT) hH
  have hJ : Continuous J := (sourceCuspHeightShellEnergy_continuousOn _ L).comp_continuous
    (sourceKPHighCuspHeight_continuous K hζ T hT) hH
  have hR : Continuous (fun q => ‖R q‖^2) :=
    (sourceKPHighCuspNonconstantEisenstein_continuous K hζ hs T hT).norm.pow 2
  have hW : Continuous W := sourceKPHighCuspNonconstantEnergy_continuous K hζ hs T hT
  have hout (q : Y) (hq : q ∉ S) : η q = 0 ∧ J q = 0 := by
    apply sourceCuspHeightShell_outside _ L (H q) hL (hH q)
    change ¬(L ≤ H q ∧ H q ≤ 8*L) at hq
    push_neg at hq
    by_cases hl : L ≤ H q
    · exact Or.inr (hq hl).le
    · exact Or.inl (le_of_not_ge hl)
  have hηs (f : Y → ℝ) : HasCompactSupport (fun q => (η q)^2*f q) := by
    apply HasCompactSupport.of_support_subset_isCompact hS
    intro q hq
    by_contra hn
    apply hq
    change (η q)^2*f q = 0
    rw [(hout q hn).1,zero_pow (by norm_num : (2 : ℕ) ≠ 0),zero_mul]
  have hJs : HasCompactSupport (fun q => J q*‖R q‖^2) := by
    apply HasCompactSupport.of_support_subset_isCompact hS
    intro q hq
    by_contra hn
    apply hq
    change J q*‖R q‖^2 = 0
    rw [(hout q hn).2,zero_mul]
  refine ⟨((hη.pow 2).mul hW).integrable_of_hasCompactSupport (hηs W),
    ((hη.pow 2).mul hR).integrable_of_hasCompactSupport (hηs _),
    (hJ.mul hR).integrable_of_hasCompactSupport hJs,?_⟩
  apply (hR.continuousOn.integrableOn_compact hS).mono_set
  intro q hq
  change 2*L < H q ∧ H q ≤ 4*L at hq
  exact ⟨by linarith [hq.1],by linarith [hq.2]⟩

end
end ArtinMatthews

/-! Integrating the actual cusp torus inequality gives a uniform height
gain over the true high-cusp quotient measure. -/
namespace ArtinMatthews
open NumberField Matrix MeasureTheory Topology Set Filter
open scoped NumberField MatrixGroups AdeleRing Classical ENNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
local notation "B" => SourceKPFiniteLevelFiber K hζ
local instance sourceCuspShellAdelicMeasurable : MeasurableSpace 𝔸[K] := borel _
local notation "ν" => sourceKPAdelicTraceProduct K
local notation "A₀" => sourceKPAdelicFundamentalDomain K
local notation "δ" => sourceKPCuspHeightGapExponent K

theorem sourceKPHighCuspProjection_upper_orbitHeight (T : ℝ) (hT : 1 < T)
    (x : SourceKPHighCuspFinite K hζ T) (y : 𝔸[K]) :
    sourceKPAutomorphicOrbitHeight K hζ
      (sourceKPHighCuspProjection K hζ T (Multiplicative.ofAdd y • x)).val =
        sourceKPFiniteLevelHeight K hζ x.val := by
  rw [sourceKPHighCuspProjection_orbitHeight K hζ T hT,sourceKPCuspHighUpper_height]

theorem sourceKPHighCusp_anisotropic_weighted (v₀ : InfinitePlace K) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (T : ℝ) (hT : 1 < T) (s : ℂ)
      (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2*s.re+1)
      (a b : ℝ) (η : ℝ → ℝ),
      let H := fun q : SourceKPHighCuspAutomorphic K hζ T => sourceKPAutomorphicOrbitHeight K hζ q.val
      let R := sourceKPHighCuspNonconstantEisenstein K hζ s T hT
      let W := fun q => (η (H q))^2 * sourceKPHighCuspNonconstantEnergy K hζ hs T hT q
      0 < a → (∀ u ∈ Ioc a b, η u = 1) →
        IntegrableOn (fun q => ‖R q‖^2) (H ⁻¹' Ioc a b) (sourceKPHighCuspMeasure K hζ T) →
        Integrable W (sourceKPHighCuspMeasure K hζ T) →
        κ*a^δ * (∫ q in H ⁻¹' Ioc a b, ‖R q‖^2 ∂sourceKPHighCuspMeasure K hζ T) ≤
          ∫ q, W q ∂sourceKPHighCuspMeasure K hζ T := by
  let rep (b : B) : SourceKPFiniteAdeleProjective K hζ := Classical.choose (QuotientGroup.mk_surjective b)
  have hrep (b : B) : QuotientGroup.mk (rep b) = b :=
    Classical.choose_spec (QuotientGroup.mk_surjective b)
  let C (b : B) := sourceKPFiniteLevelHeight K hζ (1,b)
  let gap (b : B) := sourceKPCuspHorizontalGapConstant K (sourceKPFixedFiniteCuspPeriod K hζ (rep b)) /
    C b ^ δ
  have hgap (b : B) : 0 < gap b :=
    div_pos (sourceKPCuspHorizontalGapConstant_pos K _
      (sourceKPFixedFiniteCuspPeriod_ne_zero K hζ (rep b)))
      (Real.rpow_pos_of_pos (sourceKPFiniteLevelHeight_pos K hζ (1,b)) _)
  let S := (sourceKPCuspFixedFiniteFibers_finite K hζ v₀).toFinset
  let G := insert (1 : ℝ) (S.image gap)
  have hG : G.Nonempty := ⟨1,Finset.mem_insert_self _ _⟩
  let κ := G.min' hG
  have hκ : 0 < κ := by
    have hmem : κ ∈ G := Finset.min'_mem _ _
    rcases Finset.mem_insert.mp hmem with h | h
    · rw [h]; norm_num
    · obtain ⟨b,_hb,hb'⟩ := Finset.mem_image.mp h
      rw [← hb']
      exact hgap b
  have hle (b : B) (hb : b ∈ sourceKPCuspFixedFiniteFibers K hζ v₀) : κ ≤ gap b := by
    apply Finset.min'_le G _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨b,?_,rfl⟩))
    exact (sourceKPCuspFixedFiniteFibers_finite K hζ v₀).mem_toFinset.mpr hb
  refine ⟨κ,hκ,?_⟩
  intro T hT s hs a b η
  dsimp only
  intro ha hη hmi hwi
  let Y := SourceKPHighCuspAutomorphic K hζ T
  let H : Y → ℝ := fun q => sourceKPAutomorphicOrbitHeight K hζ q.val
  let R := sourceKPHighCuspNonconstantEisenstein K hζ s T hT
  let E := sourceKPHighCuspNonconstantEnergy K hζ hs T hT
  let J := H ⁻¹' Ioc a b
  let M := J.indicator (fun q => ‖R q‖ ^ 2)
  let W : Y → ℝ := fun q => (η (H q))^2 * E q
  let μ := sourceKPHighCuspMeasure K hζ T
  have hJ : MeasurableSet J := by
    change MeasurableSet ((Subtype.val : Y → SourceKPAutomorphicLevel K hζ) ⁻¹'
      ({q | a < sourceKPAutomorphicOrbitHeight K hζ q} ∩ {q | sourceKPAutomorphicOrbitHeight K hζ q ≤ b}))
    exact ((sourceKPHighCuspAutomorphic_isOpen K hζ a).measurableSet.inter
      (sourceKPAutomorphicOrbitHeight_sublevel_closed K hζ b).measurableSet).preimage measurable_subtype_coe
  have hm : Integrable M μ := hmi.integrable_indicator hJ
  have hw : Integrable W μ := hwi
  obtain ⟨F,hF,hfib,hinj,hcover⟩ := sourceKPCuspFixedFiniteFibers_exists_section K hζ v₀ T
  have hmav := sourceKPCuspHighSection_average_integral_real K hζ T hT F hF hinj hcover M hm
  have hwav := sourceKPCuspHighSection_average_integral_real K hζ T hT F hF hinj hcover W hw
  let μF := sourceKPHighRepresentativeHaar K hζ T
  let U (y : 𝔸[K]) (x : SourceKPHighCuspFinite K hζ T) :=
    sourceKPHighCuspProjection K hζ T (Multiplicative.ofAdd y • x)
  let Mavg (x : SourceKPHighCuspFinite K hζ T) := ∫ y in A₀, M (U y x) ∂ν
  let Wavg (x : SourceKPHighCuspFinite K hζ T) := ∫ y in A₀, W (U y x) ∂ν
  let : IsFiniteMeasure ((ν).restrict A₀) := by
    constructor
    rw [Measure.restrict_apply_univ,sourceKPAdelicTraceProduct_fundamentalDomain_of_primitiveRoot K hζ]
    exact ENNReal.one_lt_top
  have hMint : Integrable Mavg (μF.restrict F) := hmav.1.integral_prod_right
  have hWint : Integrable Wavg (μF.restrict F) := hwav.1.integral_prod_right
  have hδ : 0 < δ := sourceKPCuspHeightGapExponent_pos K hζ
  have hlocal (x : SourceKPHighCuspFinite K hζ T) (hx : x ∈ F) :
      κ*a^δ * Mavg x ≤ Wavg x := by
    let h := sourceKPFiniteLevelHeight K hζ x.val
    have hh (y : 𝔸[K]) : H (U y x) = h :=
      sourceKPHighCuspProjection_upper_orbitHeight K hζ T hT x y
    by_cases hJx : h ∈ Ioc a b
    · have hJ' (y : 𝔸[K]) : U y x ∈ J := by
        change H (U y x) ∈ Ioc a b
        rw [hh y]
        exact hJx
      have hmfun (y : 𝔸[K]) : M (U y x) = ‖R (U y x)‖^2 := Set.indicator_of_mem (hJ' y) _
      have hwfun (y : 𝔸[K]) : W (U y x) = E (U y x) := by
        change (η (H (U y x)))^2 * E (U y x) = _
        rw [hh y,hη h hJx,one_pow,one_mul]
      have hco : κ*a^δ ≤ gap x.val.2 * h^δ :=
        mul_le_mul (hle x.val.2 (hfib x hx))
          (Real.rpow_le_rpow ha.le hJx.1.le hδ.le) (Real.rpow_nonneg ha.le _) (hgap _).le
      have hgapx := (sourceKPHighCusp_trace_anisotropic K hζ (rep x.val.2) T x (hrep x.val.2) hs hT).2.2
      have hMpos : 0 ≤ ∫ y in A₀, ‖R (U y x)‖^2 ∂ν := integral_nonneg (fun _ => sq_nonneg _)
      dsimp only [Mavg,Wavg]
      simp only [hmfun,hwfun]
      exact (mul_le_mul_of_nonneg_right hco hMpos).trans hgapx
    · have hmzero (y : 𝔸[K]) : M (U y x) = 0 := by
        apply Set.indicator_of_notMem
        change H (U y x) ∉ Ioc a b
        rw [hh y]
        exact hJx
      dsimp only [Mavg,Wavg]
      simp only [hmzero,integral_zero,mul_zero]
      apply integral_nonneg
      intro y
      exact mul_nonneg (sq_nonneg _) (sourceKPHighCuspNonconstantEnergy_nonneg K hζ hs T hT (U y x))
  change κ*a^δ * (∫ q in J, ‖R q‖^2 ∂μ) ≤ ∫ q, W q ∂μ
  rw [← integral_indicator hJ]
  change κ*a^δ * (∫ q, M q ∂μ) ≤ _
  rw [hmav.2,hwav.2,← integral_const_mul]
  apply integral_mono_ae (hMint.const_mul _) hWint
  filter_upwards [ae_restrict_mem hF] with x hx
  exact hlocal x hx

end
end ArtinMatthews

/-! All shell mass integrals are taken on the literal automorphic measure.
The high subtype and full framed quotient have identical restricted masses. -/
namespace ArtinMatthews
open NumberField Matrix MeasureTheory Topology Set Filter
open scoped NumberField MatrixGroups AdeleRing ENNReal
noncomputable section

theorem dyadicL2OpenShell_three_union {Y : Type*} (H : Y → ℝ) {A : ℝ} (hA : 0 < A) (n : ℕ) :
    (dyadicL2OpenShell H A n ∪ dyadicL2OpenShell H A (n+1)) ∪ dyadicL2OpenShell H A (n+2) =
      {q | A*2^n < H q ∧ H q ≤ A*2^(n+3)} := by
  have hmono : Monotone (fun k : ℕ => A*(2 : ℝ)^k) := fun _ _ h =>
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) h) hA.le
  have h01 := hmono (Nat.le_succ n)
  have h12 := hmono (Nat.le_succ (n+1))
  have h23 := hmono (Nat.le_succ (n+2))
  ext q
  change (((A*2^n < H q ∧ H q ≤ A*2^(n+1)) ∨
    (A*2^(n+1) < H q ∧ H q ≤ A*2^(n+2))) ∨
    (A*2^(n+2) < H q ∧ H q ≤ A*2^(n+3))) ↔ _
  constructor
  · rintro ((h | h) | h)
    · exact ⟨h.1,h.2.trans (h12.trans h23)⟩
    · exact ⟨h01.trans_lt h.1,h.2.trans h23⟩
    · exact ⟨(h01.trans h12).trans_lt h.1,h.2⟩
  · intro h
    by_cases h₁ : H q ≤ A*2^(n+1)
    · exact Or.inl (Or.inl ⟨h.1,h₁⟩)
    · by_cases h₂ : H q ≤ A*2^(n+2)
      · exact Or.inl (Or.inr ⟨lt_of_not_ge h₁,h₂⟩)
      · exact Or.inr ⟨lt_of_not_ge h₂,h.2⟩

theorem dyadicL2OpenShell_three_integral {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) (H : Y → ℝ) (hH : Measurable H) {A : ℝ} (hA : 0 < A)
    (F : Y → ℝ) (hF : ∀ n, IntegrableOn F (dyadicL2OpenShell H A n) μ) (n : ℕ) :
    (∫ q in {q | A*2^n < H q ∧ H q ≤ A*2^(n+3)}, F q ∂μ) =
      (∫ q in dyadicL2OpenShell H A n, F q ∂μ) +
      (∫ q in dyadicL2OpenShell H A (n+1), F q ∂μ) +
      (∫ q in dyadicL2OpenShell H A (n+2), F q ∂μ) := by
  have hd := dyadicL2OpenShell_pairwise H hA
  have h₀₁ := hd (show n ≠ n+1 by omega)
  have h₀₂ := hd (show n ≠ n+2 by omega)
  have h₁₂ := hd (show n+1 ≠ n+2 by omega)
  rw [← dyadicL2OpenShell_three_union H hA n,
    setIntegral_union (disjoint_union_left.mpr ⟨h₀₂,h₁₂⟩)
      (dyadicL2OpenShell_measurable H hH A (n+2)) ((hF n).union (hF (n+1))) (hF (n+2)),
    setIntegral_union h₀₁ (dyadicL2OpenShell_measurable H hH A (n+1)) (hF n) (hF (n+1))]

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
local notation "X" => SourceKPAutomorphicLevel K hζ
local notation "H" => sourceKPAutomorphicOrbitHeight K hζ
local notation "μ" => sourceKPAutomorphicMeasure K hζ (sourceKPArchHaar K hζ)

theorem sourceKPHighCuspMeasure_map_val_restrict_set (T : ℝ) (S : Set X)
    (hS : MeasurableSet S) (hSub : S ⊆ {q | T < H q}) :
    Measure.map Subtype.val ((sourceKPHighCuspMeasure K hζ T).restrict (Subtype.val ⁻¹' S)) =
      (μ).restrict S := by
  have hval : MeasurableEmbedding
      (Subtype.val : SourceKPHighCuspAutomorphic K hζ T → X) :=
    MeasurableEmbedding.subtype_coe (sourceKPHighCuspAutomorphic_isOpen K hζ T).measurableSet
  rw [← hval.restrict_map _ S,sourceKPHighCuspMeasure_map_val,Measure.restrict_restrict hS,
    Set.inter_eq_left.mpr hSub]

theorem sourceKPHighCuspRemainder_shell_mass_eq {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (T : ℝ) (hT : 1 < T) (A : ℝ) (hTA : T ≤ A) (n : ℕ) :
    let Y := SourceKPHighCuspAutomorphic K hζ T
    let R := sourceKPHighCuspNonconstantEisenstein K hζ s T hT
    (∫ q in dyadicL2OpenShell (fun q : Y => H q.val) A n,
      ‖R q‖^2 ∂sourceKPHighCuspMeasure K hζ T) =
      ∫ q in dyadicL2OpenShell H A n, ‖sourceKPHighRemainderExtension K hζ s T hT q‖^2 ∂μ := by
  dsimp only
  let S := dyadicL2OpenShell H A n
  let Y := SourceKPHighCuspAutomorphic K hζ T
  let v : Y → X := Subtype.val
  let f := fun q => ‖sourceKPHighRemainderExtension K hζ s T hT q‖^2
  have hF : Measurable f := (sourceKPHighRemainderExtension_measurable K hζ hs T hT).norm.pow_const 2
  have hA : 0 < A := (zero_lt_one.trans hT).trans_le hTA
  have hS : MeasurableSet S := sourceKPDyadicOpenShell_measurable K hζ A n
  have hSub : S ⊆ {q | T < H q} := by
    intro q hq
    have ha : A ≤ A*(2 : ℝ)^n := by
      simpa only [one_mul,mul_one] using mul_le_mul_of_nonneg_left
        (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := n)) hA.le
    exact (hTA.trans ha).trans_lt hq.1
  have hmap := sourceKPHighCuspMeasure_map_val_restrict_set K hζ T S hS hSub
  have hf (q : Y) : ‖sourceKPHighCuspNonconstantEisenstein K hζ s T hT q‖^2 = f (v q) := by
    change _ = ‖sourceKPHighRemainderExtension K hζ s T hT q.val‖^2
    rw [sourceKPHighRemainderExtension_apply K hζ s T hT q]
  change (∫ q in v ⁻¹' S, ‖sourceKPHighCuspNonconstantEisenstein K hζ s T hT q‖^2
      ∂sourceKPHighCuspMeasure K hζ T) = _
  simp_rw [hf]
  rw [← integral_map measurable_subtype_coe.aemeasurable hF.aestronglyMeasurable,hmap]

theorem sourceKPHighCuspRemainder_shell_integrable {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (T : ℝ) (hT : 1 < T) (A : ℝ) (hTA : T < A) (n : ℕ) :
    IntegrableOn (fun q => ‖sourceKPHighCuspNonconstantEisenstein K hζ s T hT q‖^2)
      (dyadicL2OpenShell (fun q : SourceKPHighCuspAutomorphic K hζ T => H q.val) A n)
      (sourceKPHighCuspMeasure K hζ T) := by
  have hA : 0 < A := (zero_lt_one.trans hT).trans hTA
  have ha : A ≤ A*(2 : ℝ)^n := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := n)) hA.le
  letI := sourceKPHighCuspMeasure_finiteOnCompacts K hζ T
  have hS := sourceKPHighCuspBand_isCompact K hζ T (A*2^n) (A*2^(n+1)) hT
    (hTA.trans_le ha) (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) (Nat.le_succ n)) hA.le)
  have hc := (sourceKPHighCuspNonconstantEisenstein_continuous K hζ hs T hT).norm.pow 2
  apply (hc.continuousOn.integrableOn_compact hS).mono_set
  intro q hq
  exact ⟨hq.1.le,hq.2⟩

end
end ArtinMatthews

/-! The exact native Caccioppoli estimate, once tested on the actual
quotient, gives the dyadic recurrence with the proved trace-dual exponent. -/
namespace ArtinMatthews
open NumberField Matrix MeasureTheory Topology Set Filter
open scoped NumberField MatrixGroups AdeleRing ENNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable {s : ℂ} (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2*s.re+1)
variable (T : ℝ) (hT : 1 < T)
local notation "X" => SourceKPAutomorphicLevel K hζ
local notation "Y" => SourceKPHighCuspAutomorphic K hζ T
local notation "H₀" => sourceKPAutomorphicOrbitHeight K hζ
local notation "H" => fun q : Y => H₀ (Subtype.val q)
local notation "μ₀" => sourceKPAutomorphicMeasure K hζ (sourceKPArchHaar K hζ)
local notation "μ" => sourceKPHighCuspMeasure K hζ T
local notation "R" => sourceKPHighCuspNonconstantEisenstein K hζ s T hT
local notation "E" => sourceKPHighCuspNonconstantEnergy K hζ hs T hT
local notation "r" => Fintype.card (InfinitePlace K)
local notation "Λ" => ((InfinitePlace.nrComplexPlaces K : ℂ)*(1-4*s^2))
local notation "δ" => sourceKPCuspHeightGapExponent K

def sourceKPHighShellEnergyEstimate (L : ℝ) : Prop :=
  (∫ q, (sourceCuspHeightShellBump L (H q))^2*E q ∂μ) ≤
    2*‖Λ‖*(∫ q, (sourceCuspHeightShellBump L (H q))^2*‖R q‖^2 ∂μ) +
      4*(∫ q, sourceCuspHeightShellEnergy r L (H q)*‖R q‖^2 ∂μ)

include hs in
private theorem sourceKPHighShell_mass_comparison (L : ℝ) (hTL : T < L)
    (C : ℝ) (hbound : ∀ u : ℝ, sourceCuspHeightShellEnergy r L u ≤ C) :
    let S := {q : Y | H q ∈ Ioc L (8*L)}
    (∫ q, (sourceCuspHeightShellBump L (H q))^2*‖R q‖^2 ∂μ) ≤ ∫ q in S, ‖R q‖^2 ∂μ ∧
    (∫ q, sourceCuspHeightShellEnergy r L (H q)*‖R q‖^2 ∂μ) ≤ C*∫ q in S, ‖R q‖^2 ∂μ := by
  dsimp only
  let S : Set Y := {q | H q ∈ Ioc L (8*L)}
  let f : Y → ℝ := fun q => ‖R q‖^2
  let η : Y → ℝ := fun q => sourceCuspHeightShellBump L (H q)
  let J : Y → ℝ := fun q => sourceCuspHeightShellEnergy r L (H q)
  have hL : 0 < L := (zero_lt_one.trans hT).trans hTL
  have hS : MeasurableSet S :=
    measurableSet_Ioc.preimage (sourceKPHighCuspHeight_continuous K hζ T hT).measurable
  letI := sourceKPHighCuspMeasure_finiteOnCompacts K hζ T
  have hB := sourceKPHighCuspBand_isCompact K hζ T L (8*L) hT hTL (by linarith)
  have hf : Continuous f := (sourceKPHighCuspNonconstantEisenstein_continuous K hζ hs T hT).norm.pow 2
  have hfi : IntegrableOn f S μ := (hf.continuousOn.integrableOn_compact hB).mono_set (fun _ h => ⟨h.1.le,h.2⟩)
  have hm := sourceKPHighShell_integrability K hζ T L hT hTL hs
  have hg₁ : Integrable (fun q => (η q)^2*f q) μ := hm.2.1
  have hg₂ : Integrable (fun q => J q*f q) μ := hm.2.2.1
  have hout (q : Y) (hq : q ∉ S) : η q = 0 ∧ J q = 0 := by
    apply sourceCuspHeightShell_outside r L (H q) hL ((zero_lt_one.trans hT).trans q.property)
    change ¬ (L < H q ∧ H q ≤ 8*L) at hq
    by_cases h : L < H q
    · exact Or.inr (lt_of_not_ge (fun h' => hq ⟨h,h'⟩)).le
    · exact Or.inl (le_of_not_gt h)
  change (∫ q, (η q)^2*f q ∂μ) ≤ (∫ q in S, f q ∂μ) ∧
    (∫ q, J q*f q ∂μ) ≤ C*(∫ q in S, f q ∂μ)
  rw [← integral_indicator hS,← integral_const_mul]
  constructor
  · apply integral_mono hg₁ (hfi.integrable_indicator hS)
    intro q
    change (η q)^2*f q ≤ S.indicator f q
    by_cases hq : q ∈ S
    · rw [Set.indicator_of_mem hq]
      exact (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (sourceCuspHeightShellBump_nonneg _ _) (sourceCuspHeightShellBump_le_one _ _) 2)
        (sq_nonneg ‖R q‖)).trans_eq (by rw [one_pow,one_mul])
    · rw [Set.indicator_of_notMem hq,(hout q hq).1]
      simp
  · apply integral_mono hg₂ ((hfi.integrable_indicator hS).const_mul C)
    intro q
    change J q*f q ≤ C*S.indicator f q
    by_cases hq : q ∈ S
    · rw [Set.indicator_of_mem hq]
      exact mul_le_mul_of_nonneg_right (hbound _) (sq_nonneg ‖R q‖)
    · rw [Set.indicator_of_notMem hq,(hout q hq).2,zero_mul,mul_zero]

theorem sourceKPHighRemainderExtension_recurrence_of_shell_energy
    (A : ℝ) (hTA : T < A)
    (hCaccioppoli : ∀ n : ℕ, sourceKPHighShellEnergyEstimate K hζ hs T hT (A*2^n)) :
    let a := fun n : ℕ => ∫ q in dyadicL2OpenShell H₀ A n,
      ‖sourceKPHighRemainderExtension K hζ s T hT q‖^2 ∂μ₀
    ∃ D : ℝ, 0 ≤ D ∧ ∀ n : ℕ,
      a (n+1) ≤ D*2^(-δ*(n+1 : ℕ))*(a n+a (n+1)+a (n+2)) := by
  dsimp only
  let v₀ : InfinitePlace K := Classical.choice inferInstance
  obtain ⟨κ,hκ,hgap⟩ := sourceKPHighCusp_anisotropic_weighted K hζ v₀
  obtain ⟨C,hC,hbound⟩ := sourceCuspHeightShellEnergy_uniform_bound K
  let B := 2*‖Λ‖+4*C
  let D := B/(κ*A^δ)
  have hA : 0 < A := (zero_lt_one.trans hT).trans hTA
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hD : 0 ≤ D := div_nonneg hB (mul_nonneg hκ.le (Real.rpow_nonneg hA.le _))
  refine ⟨D,hD,?_⟩
  intro n
  let L := A*(2 : ℝ)^n
  have hAL : A ≤ L := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := n)) hA.le
  have hTL : T < L := hTA.trans_le hAL
  have hL : 0 < L := hA.trans_le hAL
  let f : Y → ℝ := fun q => ‖R q‖^2
  let a (j : ℕ) := ∫ q in dyadicL2OpenShell H A j, f q ∂μ
  let m := ∫ q in {q : Y | H q ∈ Ioc L (8*L)}, f q ∂μ
  have h₂ : 2*L = A*2^(n+1) := by dsimp only [L]; rw [pow_succ]; ring
  have h₄ : 4*L = A*2^(n+2) := by dsimp only [L]; rw [pow_add]; norm_num; ring
  have h₈ : 8*L = A*2^(n+3) := by dsimp only [L]; rw [pow_add]; norm_num; ring
  have hm : m = a n+a (n+1)+a (n+2) := by
    dsimp only [m,a]
    rw [h₈]
    exact dyadicL2OpenShell_three_integral μ H
      (sourceKPHighCuspHeight_continuous K hζ T hT).measurable hA f
      (sourceKPHighCuspRemainder_shell_integrable K hζ hs T hT A hTA) n
  have hshell := sourceKPHighShell_integrability K hζ T L hT hTL hs
  have he := hgap T hT s hs (2*L) (4*L) (sourceCuspHeightShellBump L)
    (by positivity) (fun u hu => sourceCuspHeightShellBump_middle L u hL hu.1.le hu.2)
    hshell.2.2.2 hshell.1
  have hc := hCaccioppoli n
  change (∫ q, (sourceCuspHeightShellBump L (H q))^2*E q ∂μ) ≤ _ at hc
  have hb := sourceKPHighShell_mass_comparison K hζ hs T hT L hTL C (hbound L)
  have hmain : κ*(2*L)^δ * a (n+1) ≤ B*m := by
    have he' : κ*(2*L)^δ * a (n+1) ≤ ∫ q, (sourceCuspHeightShellBump L (H q))^2*E q ∂μ := by
      change κ*(2*L)^δ * (∫ q in H ⁻¹' Ioc (A*2^(n+1)) (A*2^(n+2)), f q ∂μ) ≤ _
      rw [← h₂,← h₄]
      exact he
    exact (he'.trans hc).trans (calc
      _ ≤ 2*‖Λ‖*m+4*(C*m) :=
        add_le_add (mul_le_mul_of_nonneg_left hb.1 (by positivity))
          (mul_le_mul_of_nonneg_left hb.2 (by norm_num))
      _ = B*m := by dsimp only [B]; ring)
  have hcpos : 0 < κ*(2*L)^δ := mul_pos hκ (Real.rpow_pos_of_pos (by positivity) _)
  have hpow : (2*L)^δ = A^δ*(2 : ℝ)^(δ*(n+1 : ℕ)) := by
    rw [h₂,Real.mul_rpow hA.le (pow_nonneg (by norm_num) _),
      ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 2
    ring
  have htwo : 0 < (2 : ℝ)^(δ*(n+1 : ℕ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hrec : a (n+1) ≤ D*2^(-δ*(n+1 : ℕ))*(a n+a (n+1)+a (n+2)) := by
    calc
      _ ≤ (B*m)/(κ*(2*L)^δ) := (le_div_iff₀ hcpos).mpr (by simpa only [mul_comm] using hmain)
      _ = D*2^(-δ*(n+1 : ℕ))*(a n+a (n+1)+a (n+2)) := by
        rw [hpow,← hm,show -δ*((n+1 : ℕ) : ℝ) = -(δ*(n+1 : ℕ)) by ring,
          Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
        dsimp only [D]
        field_simp [hκ.ne',htwo.ne',(Real.rpow_pos_of_pos hA δ).ne']
        <;> ring
  dsimp only [a,f] at hrec
  simp only [sourceKPHighCuspRemainder_shell_mass_eq K hζ hs T hT A hTA.le] at hrec
  exact hrec

theorem sourceKPHighRemainderExtension_memLp_of_shell_energy (hT₂ : 2 ≤ T)
    (A : ℝ) (hTA : T < A)
    (hCaccioppoli : ∀ n : ℕ, sourceKPHighShellEnergyEstimate K hζ hs T hT (A*2^n)) :
    MemLp (sourceKPHighRemainderExtension K hζ s T hT) 2 ((μ₀).restrict {q | A < H₀ q}) := by
  obtain ⟨D,hD,hrec⟩ := sourceKPHighRemainderExtension_recurrence_of_shell_energy K hζ hs T hT A hTA hCaccioppoli
  obtain ⟨C,hC,hgrowth⟩ := sourceKPHighRemainderExtension_dyadic_mass_growth K hζ hs T hT hT₂ A hTA.le
  exact memLp_high_of_dyadicOpen_recurrence μ₀ H₀ ((zero_lt_one.trans hT).trans hTA)
    (sourceKPHighRemainderExtension K hζ s T hT)
    (sourceKPHighRemainderExtension_dyadic_memLp K hζ hs T hT hT₂ A hTA.le)
    δ D (2*s.re+1) C (sourceKPCuspHeightGapExponent_pos K hζ) hD hC hgrowth hrec

end
end ArtinMatthews
