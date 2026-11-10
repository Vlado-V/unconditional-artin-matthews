module

public import ArtinMatthews.SourcePrincipalContourAnalytic
public import ArtinMatthews.SourceLogRadialShear
public import ArtinMatthews.SourcePrincipalContourBounds
public import ArtinMatthews.SourcePrincipalContourGeometry
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Actual principal contour integrability with the source scales kept outside the height bounds. -/

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain Set MeasureTheory
open VaryingKummerAnalytic QuadraticWeil SourcePhysical
open scoped NumberField Classical
noncomputable section

private theorem integral_majorized {A : Type*} [MeasurableSpace A] {μ : Measure A}
    {f : A → ℂ} {g : A → ℝ} (c : ℂ) (B : ℝ)
    (hf : AEStronglyMeasurable f μ) (hg : Integrable g μ) (hbound : ∀ p, ‖f p‖ ≤ B * g p) :
    Integrable f μ ∧ ‖c * ∫ p, f p ∂μ‖ ≤ ‖c‖ * B * ∫ p, g p ∂μ := by
  have hi : Integrable f μ := (hg.const_mul B).mono' hf (ae_of_all _ hbound)
  refine ⟨hi, ?_⟩
  rw [norm_mul, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  calc
    _ ≤ ∫ p, ‖f p‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ p, B * g p ∂μ := integral_mono hi.norm (hg.const_mul B) hbound
    _ = _ := integral_const_mul B g

local notation "H" => sourceContourHeightWeight
local notation "G" => (fun x : ℝ => Real.exp (-(x ^ 2)))

private theorem heightGaussianIntegrable : Integrable G := by
  simpa using integrable_exp_neg_mul_sq (b := 1) (by norm_num)

private theorem height3Integrable :
    Integrable (fun p : SourcePoissonHeights => (H p.1.1 * H p.1.2) * G (p.2 + p.1.2))
      sourcePoissonHeightMeasure := by
  have hH := sourceContourHeightWeight_integrable
  have hp := (hH.mul_prod hH).mul_prod heightGaussianIntegrable
  have hs := sourceLogRadial_shear_measurePreserving ((volume : Measure ℝ).prod volume)
    (Prod.snd : ℝ × ℝ → ℝ) measurable_snd
  exact hs.integrable_comp_of_integrable hp

private theorem height2Integrable :
    Integrable (fun p : ℝ × ℝ => H p.1 * G (p.2 + p.1)) ((volume : Measure ℝ).prod volume) := by
  have hs := sourceLogRadial_shear_measurePreserving (volume : Measure ℝ) (id : ℝ → ℝ) measurable_id
  exact hs.integrable_comp_of_integrable (sourceContourHeightWeight_integrable.mul_prod heightGaussianIntegrable)

variable (F : Type) [Field F] [NumberField F]
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
variable {J : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F J)
variable (v : InfinitePlace F)
local notation "S" => sourceHilbertSet F S₀

def sourcePrincipalPoissonKernelOnLines (X Y Z a b c : ℝ) (p : SourcePoissonHeights) : ℂ :=
  sourcePrincipalPoissonKernel F hζ S₀ η v X Y Z
    (sourcePoissonVertical a p.2, sourcePoissonVertical b p.1.1, sourcePoissonVertical c p.1.2)

def sourcePrincipalPoissonWResidueOnLines (X Y Z a c : ℝ) (p : ℝ × ℝ) : ℂ :=
  sourcePrincipalPoissonWResidue F hζ S₀ η v X Y Z
    (sourcePoissonVertical a p.2) (sourcePoissonVertical c p.1)

def sourcePrincipalPoissonIntegral (X Y Z a b c : ℝ) : ℂ :=
  sourcePoissonNormalization ^ 3 * ∫ p, sourcePrincipalPoissonKernelOnLines F hζ S₀ η v X Y Z a b c p
    ∂sourcePoissonHeightMeasure

def sourcePrincipalPoissonResidueIntegral (X Y Z a c : ℝ) : ℂ :=
  sourcePoissonNormalization ^ 2 * ∫ p,
    sourcePrincipalPoissonWResidueOnLines F hζ S₀ η v X Y Z a c p ∂((volume : Measure ℝ).prod volume)

theorem sourcePrincipalPoissonKernelOnLines_continuous
    (hJ : J ≠ ⊥) (hcut : principalAngularCutoff F J ⊆ S)
    {X Y Z : ℝ} (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    {a b c : ℝ} (ha : sourcePrincipalSigma ≤ a) (hb : 95 / 100 ≤ b) (hc : 16 / 100 ≤ c)
    (hb₀ : b ≠ 1) (hc₀ : c ≠ 1 / 6) :
    Continuous (sourcePrincipalPoissonKernelOnLines F hζ S₀ η v X Y Z a b c) := by
  let D := sourcePrincipalContourDomain ∩ {q : ProbeCoordinates | q.2.1 ≠ 1 ∧ q.2.2 ≠ 1 / 6}
  have hK := (sourcePrincipalPoissonKernel_differentiableOn_path F hζ S₀ η v hJ hcut hX hY hZ
    (id : ProbeCoordinates → ProbeCoordinates) (differentiableOn_id (s := D))
    (fun _ h => h.1) (fun _ h => h.2.1) (fun _ h => h.2.2)).continuousOn
  let L (p : SourcePoissonHeights) := (sourcePoissonVertical a p.2,
    sourcePoissonVertical b p.1.1, sourcePoissonVertical c p.1.2)
  have hL : Continuous L := by unfold L sourcePoissonVertical; fun_prop
  exact hK.comp_continuous hL (fun p => ⟨sourcePrincipalContourDomain_vertical ha hb hc p.2 p.1.1 p.1.2,
    sourcePrincipalVertical_w_ne_one hb₀ p.1.1, sourcePrincipalVertical_z_ne_sixth hc₀ p.1.2⟩)

theorem sourcePrincipalPoissonWResidueOnLines_continuous
    (hJ : J ≠ ⊥) (hcut : principalAngularCutoff F J ⊆ S)
    {X Y Z : ℝ} (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    {a c : ℝ} (ha : sourcePrincipalSigma ≤ a) (hc : 16 / 100 ≤ c) (hc₀ : c ≠ 1 / 6) :
    Continuous (sourcePrincipalPoissonWResidueOnLines F hζ S₀ η v X Y Z a c) := by
  let D := sourcePrincipalContourDomain ∩ {q : ProbeCoordinates | q.2.2 ≠ 1 / 6}
  let A := sourcePrincipalPoissonWRegularized F hζ S₀ η v X Y Z
  have hA : ContinuousOn A D :=
    (sourcePrincipalPoissonWRegularized_differentiableOn_path F hζ S₀ η v hJ hcut hX hY hZ
      (id : ProbeCoordinates → ProbeCoordinates) (differentiableOn_id (s := D))
      (fun _ h => h.1) (fun _ h => h.2)).continuousOn
  let L (p : ℝ × ℝ) := (sourcePoissonVertical a p.2, (1 : ℂ), sourcePoissonVertical c p.1)
  have hL : Continuous L := by unfold L sourcePoissonVertical; fun_prop
  have hm : MapsTo L univ D := by
    intro p _
    refine ⟨?_, sourcePrincipalVertical_z_ne_sixth hc₀ p.1⟩
    simpa [L, sourcePoissonVertical] using
      sourcePrincipalContourDomain_vertical ha (by norm_num : (95 / 100 : ℝ) ≤ 1) hc p.2 0 p.1
  have hcont : Continuous (fun p : ℝ × ℝ => A (L p)) :=
    hA.comp_continuous hL (fun p => hm (mem_univ p))
  have he : (fun p : ℝ × ℝ => A (L p)) = sourcePrincipalPoissonWResidueOnLines F hζ S₀ η v X Y Z a c :=
    funext fun p => sourcePrincipalPoissonWRegularized_one F hζ S₀ η v X Y Z
      (sourcePoissonVertical a p.2) (sourcePoissonVertical c p.1)
  exact he ▸ hcont

theorem sourcePrincipalPoissonIntegral_integrable_and_bound
    (hJ : J ≠ ⊥) (hcut : principalAngularCutoff F J ⊆ S)
    {a b c : ℝ} (ha : sourcePrincipalSigma ≤ a) (hb : b ∈ Icc (95 / 100 : ℝ) 4)
    (hc : c ∈ Icc (16 / 100 : ℝ) 2) (hb₀ : b ≠ 1) (hc₀ : c ≠ 1 / 6) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {X Y Z : ℝ}, 0 < X → 0 < Y → 0 < Z →
      Integrable (sourcePrincipalPoissonKernelOnLines F hζ S₀ η v X Y Z a b c) sourcePoissonHeightMeasure ∧
        ‖sourcePrincipalPoissonIntegral F hζ S₀ η v X Y Z a b c‖ ≤
          C * sourcePoissonTripleScale X Y Z a b c := by
  have hbδ : 0 < |b - 1| := abs_pos.mpr (sub_ne_zero.mpr hb₀)
  have hcδ : 0 < |6 * c - 1| := abs_pos.mpr (fun h => hc₀ (by linarith))
  obtain ⟨B, hB, hbound⟩ :=
    sourcePrincipalPoissonKernel_height_bound F hζ S₀ η v hcut _ _ hbδ hcδ
  let g (p : SourcePoissonHeights) := (H p.1.1 * H p.1.2) * G (p.2 + p.1.2)
  let m := ‖sourcePoissonNormalization ^ 3‖
  have hg0 (p : SourcePoissonHeights) : 0 ≤ g p :=
    mul_nonneg (mul_nonneg (sourceContourHeightWeight_nonneg _) (sourceContourHeightWeight_nonneg _))
      (Real.exp_nonneg _)
  refine ⟨m * B * ∫ p, g p ∂sourcePoissonHeightMeasure,
    mul_nonneg (mul_nonneg (norm_nonneg _) hB) (integral_nonneg hg0), ?_⟩
  intro X Y Z hX hY hZ
  have hm := (sourcePrincipalPoissonKernelOnLines_continuous F hζ S₀ η v hJ hcut
    hX hY hZ ha hb.1 hc.1 hb₀ hc₀).aestronglyMeasurable (μ := sourcePoissonHeightMeasure)
  obtain ⟨hi, he⟩ := integral_majorized (sourcePoissonNormalization ^ 3)
    (B * sourcePoissonTripleScale X Y Z a b c) hm (show Integrable g sourcePoissonHeightMeasure from height3Integrable)
    (fun p => hbound hX hY hZ a ha b hb c hc p.2 p.1.1 p.1.2
      (sourcePrincipalVertical_w_gap_re b p.1.1) (sourcePrincipalVertical_z_gap_re c p.1.2))
  exact ⟨hi, he.trans_eq (by dsimp only [m]; ring)⟩

theorem sourcePrincipalPoissonResidueIntegral_integrable_and_bound
    (hJ : J ≠ ⊥) (hcut : principalAngularCutoff F J ⊆ S)
    {a c : ℝ} (ha : sourcePrincipalSigma ≤ a) (hc : c ∈ Icc (16 / 100 : ℝ) 2) (hc₀ : c ≠ 1 / 6) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {X Y Z : ℝ}, 0 < X → 0 < Y → 0 < Z →
      Integrable (sourcePrincipalPoissonWResidueOnLines F hζ S₀ η v X Y Z a c)
        ((volume : Measure ℝ).prod volume) ∧
      ‖sourcePrincipalPoissonResidueIntegral F hζ S₀ η v X Y Z a c‖ ≤
        C * sourcePoissonTripleScale X Y Z a 1 c := by
  have hcδ : 0 < |6 * c - 1| := abs_pos.mpr (fun h => hc₀ (by linarith))
  obtain ⟨B, hB, hbound⟩ :=
    sourcePrincipalPoissonWResidue_height_bound F hζ S₀ η v hcut _ hcδ
  let μ : Measure (ℝ × ℝ) := (volume : Measure ℝ).prod (volume : Measure ℝ)
  let g (p : ℝ × ℝ) := H p.1 * G (p.2 + p.1)
  let m := ‖sourcePoissonNormalization ^ 2‖
  have hg0 (p : ℝ × ℝ) : 0 ≤ g p :=
    mul_nonneg (sourceContourHeightWeight_nonneg _) (Real.exp_nonneg _)
  refine ⟨m * B * ∫ p, g p ∂μ, mul_nonneg (mul_nonneg (norm_nonneg _) hB) (integral_nonneg hg0), ?_⟩
  intro X Y Z hX hY hZ
  have hm := (sourcePrincipalPoissonWResidueOnLines_continuous F hζ S₀ η v hJ hcut
    hX hY hZ ha hc.1 hc₀).aestronglyMeasurable (μ := μ)
  obtain ⟨hi, he⟩ := integral_majorized (sourcePoissonNormalization ^ 2)
    (B * sourcePoissonTripleScale X Y Z a 1 c) hm (show Integrable g μ from height2Integrable)
    (fun p => hbound hX hY hZ a ha c hc p.2 p.1 (sourcePrincipalVertical_z_gap_re c p.1))
  exact ⟨hi, he.trans_eq (by dsimp only [m]; ring)⟩

end
end ArtinMatthews.SourceEulerAssembly
