module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.RepresentationTheory.Weil.Local.QuadraticFourier
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
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
public import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected
public import Mathlib.Topology.Sheaves.Init
public import Mathlib.Topology.UniformSpace.Uniformizable
public import OAI.RepresentationTheory.Weil.Local.CompactCharacter
public import OAI.RepresentationTheory.Weil.Local.FourierTools
public import OAI.RepresentationTheory.Weil.Local.GaussianCompact
public import OAI.RepresentationTheory.Weil.Local.GaussianNonarchimedean
public import OAI.RepresentationTheory.Weil.Local.NonarchimedeanHaar
public import OAI.RepresentationTheory.Weil.Local.NonarchimedeanTestSpace


set_option backward.privateInPublic true
@[expose] public section

/-! # Fresnel Limit -/

namespace OAI.RepresentationTheory.Weil.Local.FresnelLimit.Construction

noncomputable section

section

/-! The Gaussian Fourier pairing, proved with compact cutoffs. -/

open _root_.MeasureTheory
open scoped Classical

theorem fourierIntegral_mul_swap
    {k : Type} [NormedField k] [MeasurableSpace k] [BorelSpace k]
    [SecondCountableTopology k] {n : ℕ}
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t))
    (μ : Measure (FunctionsMetaplectic.Construction.Position k n)) [SigmaFinite μ]
    {f g : FunctionsMetaplectic.Construction.Position k n → ℂ} (hf : Integrable f μ) (hg : Integrable g μ) :
    (∫ x, FunctionsMetaplectic.Construction.fourierIntegral ψ μ f x * g x ∂μ) =
      ∫ x, f x * FunctionsMetaplectic.Construction.fourierIntegral ψ μ g x ∂μ := by
  have hflip : (dotProductBilin k k : FunctionsMetaplectic.Construction.Position k n →ₗ[k] FunctionsMetaplectic.Construction.Position k n →ₗ[k] k).flip =
      dotProductBilin k k := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    exact FourierTools.Construction.dot_comm y x
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (FourierTools.Construction.circleCharacter_continuous ψ hu hc) (FourierTools.Construction.dotProductBilin_continuous n) hf hg
  rw [hflip, ← FourierTools.Construction.fourierIntegral_eq_vectorFourier ψ hu, ← FourierTools.Construction.fourierIntegral_eq_vectorFourier ψ hu] at h
  exact h

theorem quadratic_one_sum {k : Type} [Field k] {n : ℕ} (x : FunctionsMetaplectic.Construction.Position k n) :
    FunctionsMetaplectic.Construction.quadratic (1 : Matrix (Fin n) (Fin n) k) x = ∑ i, x i ^ 2 / 2 := by
  simp [FunctionsMetaplectic.Construction.quadratic, Matrix.one_apply, pow_two, Finset.sum_div]

def tensorCompactQuadratic
    {k : Type} [Field k] (n : ℕ) (ψ : AddChar k ℂ) (W : Set k) : FunctionsMetaplectic.Construction.Position k n → ℂ :=
  fun x => ∏ i, QuadraticFourier.Construction.compactQuadraticFunction ψ W 1 (x i)

theorem tensorCompactQuadratic_on
    {k : Type} [Field k] {n : ℕ} (ψ : AddChar k ℂ) (W : Set k)
    (x : FunctionsMetaplectic.Construction.Position k n) (hx : ∀ i, x i ∈ W) :
    tensorCompactQuadratic n ψ W x = ψ (FunctionsMetaplectic.Construction.quadratic 1 x) := by
  simp only [tensorCompactQuadratic, QuadraticFourier.Construction.compactQuadraticFunction, Set.indicator_of_mem (hx _), one_mul]
  rw [quadratic_one_sum, CompactCharacter.Construction.character_finset_sum]

theorem tensorCompactQuadratic_compactSupport
    {k : Type} [NormedField k] {n : ℕ} (ψ : AddChar k ℂ)
    (W : Set k) (hW : IsCompact W) : HasCompactSupport (tensorCompactQuadratic n ψ W) := by
  apply HasCompactSupport.intro (isCompact_pi_infinite fun _ : Fin n => hW)
  intro x hx
  change ¬ ∀ i, x i ∈ W at hx
  push Not at hx
  obtain ⟨i, hi⟩ := hx
  exact Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)

theorem tensorCompactQuadratic_locallyConstant
    {k : Type} [NormedField k] [NonarchimedeanAddGroup k] {n : ℕ}
    (ψ : AddChar k ℂ) (hu : ∀ t, ‖ψ t‖ = 1) (hc : Continuous (fun t => ψ t))
    (W : OpenAddSubgroup k) : IsLocallyConstant (tensorCompactQuadratic n ψ W) := by
  change IsLocallyConstant (fun x : FunctionsMetaplectic.Construction.Position k n => ∏ i, QuadraticFourier.Construction.compactQuadraticFunction ψ W 1 (x i))
  have hprod (s : Finset (Fin n)) :
      IsLocallyConstant (fun x : FunctionsMetaplectic.Construction.Position k n => ∏ i ∈ s, QuadraticFourier.Construction.compactQuadraticFunction ψ W 1 (x i)) := by
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.prod_empty, Function.const_def] using! (IsLocallyConstant.const (1 : ℂ))
    | @insert i s hi ih =>
      simp only [Finset.prod_insert hi]
      exact ((GaussianCompact.Construction.compactQuadratic_locallyConstant ψ hu hc W 1).comp_continuous
        (continuous_apply i)).mul ih
  exact hprod Finset.univ

theorem fourier_tensorCompactQuadratic_on
    {k : Type} [NormedField k] [CharZero k] [MeasurableSpace k] [BorelSpace k]
    [SecondCountableTopology k] {n : ℕ}
    (ψ : AddChar k ℂ) (μ : Measure k) [μ.IsAddHaarMeasure] [SigmaFinite μ]
    (W : OpenAddSubgroup k) (x : FunctionsMetaplectic.Construction.Position k n) (hx : ∀ i, x i ∈ W) :
    FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin n => μ)) (tensorCompactQuadratic n ψ W) x =
      (∫ y in (W : Set k), ψ (y ^ 2 / 2) ∂μ) ^ n * ψ (-FunctionsMetaplectic.Construction.quadratic 1 x) := by
  unfold tensorCompactQuadratic
  rw [FourierTensor.Construction.fourierIntegral_product]
  have hF (i : Fin n) : FourierTensor.Construction.scalarFourierIntegral ψ μ (QuadraticFourier.Construction.compactQuadraticFunction ψ W 1) (x i) =
      ψ (-(x i ^ 2 / 2)) * ∫ y in (W : Set k), ψ (y ^ 2 / 2) ∂μ := by
    simpa only [one_mul] using QuadraticFourier.Construction.scalarFourier_compactQuadratic ψ μ W 1 (x i) (hx i)
  simp only [hF, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [quadratic_one_sum, ← Finset.sum_neg_distrib, CompactCharacter.Construction.character_finset_sum, mul_comm]

theorem nonarchimedean_fresnel_pairing
    {k : Type} [NormedField k] [LocallyCompactSpace k] [NonarchimedeanAddGroup k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k) {n : ℕ}
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t)) (hn : ∃ t : k, ψ t ≠ 1)
    (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) :
    (∫ x, FunctionsMetaplectic.Construction.fourierIntegral ψ (FunctionsMetaplectic.Construction.positionMeasure k n ψ) f.val x * ψ (FunctionsMetaplectic.Construction.quadratic 1 x)
      ∂ FunctionsMetaplectic.Construction.positionMeasure k n ψ) =
      FunctionsMetaplectic.Construction.gaussianIndex k ψ 1 ^ n * ∫ x, f.val x * ψ (-FunctionsMetaplectic.Construction.quadratic 1 x) ∂ FunctionsMetaplectic.Construction.positionMeasure k n ψ := by
  let : SecondCountableTopology k := FunctionsMetaplectic.Construction.localField_secondCountable k hNondiscrete
  let μ := FunctionsMetaplectic.Construction.selfDualMeasure k ψ
  let : μ.IsAddHaarMeasure := NonarchimedeanHaar.Construction.nonarchimedean_selfDualMeasure_isAddHaarMeasure hNondiscrete ψ hu hc hn
  let μn := FunctionsMetaplectic.Construction.positionMeasure k n ψ
  let : μn.IsAddHaarMeasure := by dsimp [μn, FunctionsMetaplectic.Construction.positionMeasure]; infer_instance
  obtain ⟨hf, hs⟩ := NonarchimedeanTestSpace.Construction.schwartzBruhat_totallyDisconnected_iff.mp f.property
  have hFs := CompactCharacter.Construction.fourierIntegral_compactSupport_of_locallyConstant hNondiscrete ψ hn μn hf hs
  let K : Set k := ⋃ i : Fin n, (fun x : FunctionsMetaplectic.Construction.Position k n => x i) ''
    (tsupport f.val ∪ tsupport (FunctionsMetaplectic.Construction.fourierIntegral ψ μn f.val))
  have hK : IsCompact K := isCompact_iUnion fun i =>
    (hs.union hFs).image (continuous_apply i)
  obtain ⟨W, hW, hKW, hG⟩ := GaussianNonarchimedean.Construction.exists_gaussian_one_cutoff hNondiscrete ψ hu hc hn K hK
  let g := tensorCompactQuadratic n ψ W
  have hgi : Integrable g μn :=
    (tensorCompactQuadratic_locallyConstant ψ hu hc W).continuous.integrable_of_hasCompactSupport
      (tensorCompactQuadratic_compactSupport ψ W hW)
  have hxW (x : FunctionsMetaplectic.Construction.Position k n) (hx : x ∈ tsupport f.val ∪ tsupport (FunctionsMetaplectic.Construction.fourierIntegral ψ μn f.val)) :
      ∀ i, x i ∈ W := fun i => hKW (Set.mem_iUnion.mpr ⟨i, ⟨x, hx, rfl⟩⟩)
  calc
    _ = ∫ x, FunctionsMetaplectic.Construction.fourierIntegral ψ μn f.val x * g x ∂μn := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        change FunctionsMetaplectic.Construction.fourierIntegral ψ μn f.val x * ψ (FunctionsMetaplectic.Construction.quadratic 1 x) = FunctionsMetaplectic.Construction.fourierIntegral ψ μn f.val x * g x
        by_cases hx : x ∈ tsupport (FunctionsMetaplectic.Construction.fourierIntegral ψ μn f.val)
        · change _ = _ * tensorCompactQuadratic n ψ W x
          rw [tensorCompactQuadratic_on ψ W x (hxW x (Or.inr hx))]
        · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul, zero_mul]
    _ = ∫ x, f.val x * FunctionsMetaplectic.Construction.fourierIntegral ψ μn g x ∂μn :=
      fourierIntegral_mul_swap ψ hu hc μn (hf.continuous.integrable_of_hasCompactSupport hs) hgi
    _ = _ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        change f.val x * FunctionsMetaplectic.Construction.fourierIntegral ψ μn g x = FunctionsMetaplectic.Construction.gaussianIndex k ψ 1 ^ n * (f.val x * ψ (-FunctionsMetaplectic.Construction.quadratic 1 x))
        by_cases hx : x ∈ tsupport f.val
        · change f.val x * FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin n => μ))
            (tensorCompactQuadratic n ψ W) x = _
          rw [fourier_tensorCompactQuadratic_on ψ μ W x (hxW x (Or.inl hx))]
          change _ * ((∫ y in (W : Set k), ψ (y ^ 2 / 2) ∂ FunctionsMetaplectic.Construction.selfDualMeasure k ψ) ^ n * _) = _
          rw [hG]
          ring
        · rw [image_eq_zero_of_notMem_tsupport hx]
          ring

end

/-! A dominated-convergence criterion for quadratic Fourier pairing. -/

open _root_.MeasureTheory Filter
open scoped _root_.Topology

theorem fresnel_pairing_of_dominated_cutoffs
    {k : Type} [NormedField k] [MeasurableSpace k] [BorelSpace k]
    [SecondCountableTopology k] {n : ℕ}
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1) (hc : Continuous (fun t => ψ t))
    (μ : Measure (FunctionsMetaplectic.Construction.Position k n)) [SigmaFinite μ]
    (g : ℝ → FunctionsMetaplectic.Construction.Position k n → ℂ) (a : ℂ) (B : ℝ)
    (hgi : ∀ᶠ ε in 𝓝[>] (0 : ℝ), Integrable (g ε) μ)
    (hgb : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ x, ‖g ε x‖ ≤ 1)
    (hgl : ∀ x, Tendsto (fun ε => g ε x) (𝓝[>] (0 : ℝ)) (𝓝 (ψ (FunctionsMetaplectic.Construction.quadratic 1 x))))
    (hFb : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ x, ‖FunctionsMetaplectic.Construction.fourierIntegral ψ μ (g ε) x‖ ≤ B)
    (hFl : ∀ x, Tendsto (fun ε => FunctionsMetaplectic.Construction.fourierIntegral ψ μ (g ε) x)
      (𝓝[>] (0 : ℝ)) (𝓝 (a * ψ (-FunctionsMetaplectic.Construction.quadratic 1 x))))
    {f : FunctionsMetaplectic.Construction.Position k n → ℂ} (hf : Integrable f μ) (hF : Integrable (FunctionsMetaplectic.Construction.fourierIntegral ψ μ f) μ) :
    (∫ x, FunctionsMetaplectic.Construction.fourierIntegral ψ μ f x * ψ (FunctionsMetaplectic.Construction.quadratic 1 x) ∂μ) =
      a * ∫ x, f x * ψ (-FunctionsMetaplectic.Construction.quadratic 1 x) ∂μ := by
  have hleft : Tendsto (fun ε : ℝ => ∫ x, FunctionsMetaplectic.Construction.fourierIntegral ψ μ f x * g ε x ∂μ)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ x, FunctionsMetaplectic.Construction.fourierIntegral ψ μ f x * ψ (FunctionsMetaplectic.Construction.quadratic 1 x) ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun x => ‖FunctionsMetaplectic.Construction.fourierIntegral ψ μ f x‖)
    · filter_upwards [hgi] with ε hε
      exact hF.aestronglyMeasurable.mul hε.aestronglyMeasurable
    · filter_upwards [hgb] with ε hε
      exact Eventually.of_forall fun x => by
        rw [norm_mul]
        exact mul_le_of_le_one_right (norm_nonneg _) (hε x)
    · exact hF.norm
    · exact Eventually.of_forall fun x => (hgl x).const_mul _
  have hright : Tendsto (fun ε : ℝ => ∫ x, f x * FunctionsMetaplectic.Construction.fourierIntegral ψ μ (g ε) x ∂μ)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ x, f x * (a * ψ (-FunctionsMetaplectic.Construction.quadratic 1 x)) ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun x => ‖f x‖ * B)
    · filter_upwards [hgi] with ε hε
      exact hf.aestronglyMeasurable.mul (FourierTools.Construction.fourierIntegral_continuous ψ hu hc μ hε).aestronglyMeasurable
    · filter_upwards [hFb] with ε hε
      exact Eventually.of_forall fun x => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hε x) (norm_nonneg _)
    · exact hf.norm.mul_const B
    · exact Eventually.of_forall fun x => (hFl x).const_mul _
  have heq := hleft.congr' (show (fun ε : ℝ => ∫ x, FunctionsMetaplectic.Construction.fourierIntegral ψ μ f x * g ε x ∂μ) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun ε => ∫ x, f x * FunctionsMetaplectic.Construction.fourierIntegral ψ μ (g ε) x ∂μ) from by
    filter_upwards [hgi] with ε hε
    exact fourierIntegral_mul_swap ψ hu hc μ hf hε)
  rw [tendsto_nhds_unique heq hright, ← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by ring

end

end OAI.RepresentationTheory.Weil.Local.FresnelLimit.Construction
