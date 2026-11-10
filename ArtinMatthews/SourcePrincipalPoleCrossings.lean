module

public import ArtinMatthews.SourcePrincipalContourAnalytic
public import OAI.NumberTheory.DirichletL.Detector.Physical
public import ArtinMatthews.SourcePrincipalContourBounds
public import ArtinMatthews.SourcePrincipalContourGeometry
public import ArtinMatthews.SourcePrincipalSimplePoleShift
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
public import Mathlib.Tactic.Basify
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

/-! The actual (w=1) and (z=1/6) shifts with proved horizontal limits. -/

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain Set
open VaryingKummerAnalytic QuadraticWeil SourcePhysical
open OAI.SevenEighths.ProbePhysical
open scoped NumberField Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
variable {J : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F J)
variable (v : InfinitePlace F)
variable (hJ : J ≠ ⊥) (hcut : principalAngularCutoff F J ⊆ sourceHilbertSet F S₀)
variable {X Y Z : ℝ} (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
local notation "σ₁" => sourcePrincipalSigma
local notation "z₁" => sourcePrincipalZetaLine
local notation "H" => sourceContourHeightWeight

include hJ hcut hX hY hZ in
theorem sourcePrincipalPoissonW_shift (u y : ℝ) :
    let ξ := sourcePoissonVertical σ₁ u
    let z := sourcePoissonVertical z₁ y
    verticalIntegral σ₁ (fun w => sourcePrincipalPoissonKernel F hζ S₀ η v X Y Z (ξ,w,z)) =
      verticalIntegral (95 / 100) (fun w => sourcePrincipalPoissonKernel F hζ S₀ η v X Y Z (ξ,w,z)) +
        sourcePrincipalPoissonWResidue F hζ S₀ η v X Y Z ξ z := by
  dsimp only
  let ξ := sourcePoissonVertical σ₁ u
  let z := sourcePoissonVertical z₁ y
  let K (w : ℂ) := sourcePrincipalPoissonKernel F hζ S₀ η v X Y Z (ξ,w,z)
  let A (w : ℂ) := sourcePrincipalPoissonWRegularized F hζ S₀ η v X Y Z (ξ,w,z)
  let D : Set ℂ := {w | 95 / 100 ≤ w.re ∧ w.re ≤ σ₁}
  let δ : ℝ := 1 / 10000000
  have hδ : 0 < δ := by norm_num [δ]
  have hab : (95 / 100 : ℝ) ≤ σ₁ := by norm_num [sourcePrincipalSigma]
  have hD : MapsTo (fun w : ℂ => (ξ,w,z)) D sourcePrincipalContourDomain := by
    intro w hw
    refine ⟨?_, ?_, ?_⟩
    · simpa [ξ] using sourcePrincipalSigma_gt_one
    · exact (by norm_num : (94999 / 100000 : ℝ) < 95 / 100).trans_le hw.1
    · simpa [z, sourcePrincipalZetaLine] using
        (by norm_num : (15999 / 100000 : ℝ) < 1 / 6 + 1 / 10000000)
  have hp : DifferentiableOn ℂ (fun w : ℂ => (ξ,w,z)) D :=
    (differentiableOn_const ξ).prodMk (differentiableOn_id.prodMk (differentiableOn_const z))
  have hA : DifferentiableOn ℂ A D :=
    sourcePrincipalPoissonWRegularized_differentiableOn_path F hζ S₀ η v hJ hcut hX hY hZ
      (fun w => (ξ,w,z)) hp hD
      (fun _ _ => sourcePrincipalVertical_z_ne_sixth sourcePrincipalZetaLine_gt_sixth.ne' y)
  obtain ⟨C, hC, hbound⟩ := sourcePrincipalPoissonKernel_height_bound F hζ S₀ η v hcut δ δ hδ hδ
  obtain ⟨B, hB, hscale⟩ := sourcePrincipalTripleScale_bounded hX hY hZ
  have hz : δ ≤ ‖(6 : ℂ) * z - 1‖ :=
    (by norm_num [δ, sourcePrincipalZetaLine] : δ ≤ |6 * z₁ - 1|).trans
      (sourcePrincipalVertical_z_gap_re z₁ y)
  have hslice (b : ℝ) (hb : b ∈ Icc (95 / 100 : ℝ) σ₁) (t : ℝ)
      (ht : δ ≤ ‖sourcePoissonVertical b t - 1‖) :
      ‖K (sourcePoissonVertical b t)‖ ≤ (C * B) * H t := by
    have hb' : b ∈ Icc (95 / 100 : ℝ) 4 := ⟨hb.1, hb.2.trans sourcePrincipalSigma_le_four⟩
    have h0 := mul_nonneg (sourceContourHeightWeight_nonneg t) (sourceContourHeightWeight_nonneg y)
    have he : Real.exp (-((u+y)^2)) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _))
    have hd : (H t * H y) * Real.exp (-((u+y)^2)) ≤ H t :=
      (mul_le_of_le_one_right h0 he).trans
        (mul_le_of_le_one_right (sourceContourHeightWeight_nonneg t) (sourceContourHeightWeight_le_one y))
    exact (hbound hX hY hZ σ₁ le_rfl b hb' z₁ sourcePrincipalZetaLine_mem u t y ht hz).trans
      (mul_le_mul (mul_le_mul_of_nonneg_left (hscale σ₁ ⟨le_rfl,sourcePrincipalSigma_le_four⟩
        b hb' z₁ sourcePrincipalZetaLine_mem) hC) hd (mul_nonneg h0 (Real.exp_nonneg _)) (mul_nonneg hC hB))
  have hK (w : ℂ) (_ : (95 / 100 : ℝ) ≤ w.re) (_ : w.re ≤ σ₁) (hw : w ≠ (1 : ℂ)) :
      K w = A w / (w - 1) := by
    dsimp only [A, K]
    rw [sourcePrincipalPoissonWRegularized_eq F hζ S₀ η v X Y Z ξ w z hw]
    exact (eq_div_iff (sub_ne_zero.mpr hw)).mpr (mul_comm _ _)
  have hL (t : ℝ) : δ ≤ ‖sourcePoissonVertical (95 / 100) t - 1‖ :=
    (by norm_num [δ] : δ ≤ |(95 / 100 : ℝ) - 1|).trans (sourcePrincipalVertical_w_gap_re _ _)
  have hR (t : ℝ) : δ ≤ ‖sourcePoissonVertical σ₁ t - 1‖ :=
    (by norm_num [δ, sourcePrincipalSigma] : δ ≤ |σ₁ - 1|).trans (sourcePrincipalVertical_w_gap_re _ _)
  have hs := source_verticalIntegral_simple_pole_of_heightWeight A K (p := 1)
    (by norm_num : (95 / 100 : ℝ) < 1) sourcePrincipalSigma_gt_one hA
    (by simpa only [Complex.ofReal_one] using hK)
    (fun t => hslice _ ⟨le_rfl,hab⟩ t (hL t))
    (fun t => hslice _ ⟨hab,le_rfl⟩ t (hR t))
    (fun b hb t ht => hslice b hb t
      ((by norm_num [δ] : δ ≤ 1).trans (ht.trans (sourcePrincipalVertical_w_gap_im b t))))
  simpa only [A, K, Complex.ofReal_one, sourcePrincipalPoissonWRegularized_one] using hs

include hJ hcut hX hY hZ in
theorem sourcePrincipalPoissonZ_shift (u : ℝ) :
    let ξ := sourcePoissonVertical σ₁ u
    verticalIntegral z₁ (sourcePrincipalPoissonWResidue F hζ S₀ η v X Y Z ξ) =
      verticalIntegral (16 / 100) (sourcePrincipalPoissonWResidue F hζ S₀ η v X Y Z ξ) +
        sourcePrincipalPoissonZRegularized F hζ S₀ η v X Y Z ξ (1 / 6) := by
  dsimp only
  let ξ := sourcePoissonVertical σ₁ u
  let K := sourcePrincipalPoissonWResidue F hζ S₀ η v X Y Z ξ
  let A := sourcePrincipalPoissonZRegularized F hζ S₀ η v X Y Z ξ
  let D : Set ℂ := {z | 16 / 100 ≤ z.re ∧ z.re ≤ z₁}
  let δ : ℝ := 1 / 10000000
  have hδ : 0 < δ := by norm_num [δ]
  have hab : (16 / 100 : ℝ) ≤ z₁ := sourcePrincipalZetaLine_mem.1
  have hD : MapsTo (fun z : ℂ => (ξ,z)) D sourcePrincipalResidueDomain := by
    intro z hz
    exact ⟨by simpa [ξ] using sourcePrincipalSigma_gt_one,
      (by norm_num : (15999 / 100000 : ℝ) < 16 / 100).trans_le hz.1⟩
  have hA : DifferentiableOn ℂ A D :=
    sourcePrincipalPoissonZRegularized_differentiableOn_path F hζ S₀ η v hJ hcut hX hY hZ
      (fun z => (ξ,z)) ((differentiableOn_const ξ).prodMk differentiableOn_id) hD
  obtain ⟨C, hC, hbound⟩ := sourcePrincipalPoissonWResidue_height_bound F hζ S₀ η v hcut δ hδ
  obtain ⟨B, hB, hscale⟩ := sourcePrincipalTripleScale_bounded hX hY hZ
  have hslice (c : ℝ) (hc : c ∈ Icc (16 / 100 : ℝ) z₁) (y : ℝ)
      (hy : δ ≤ ‖(6 : ℂ) * sourcePoissonVertical c y - 1‖) :
      ‖K (sourcePoissonVertical c y)‖ ≤ (C * B) * H y := by
    have hc' : c ∈ Icc (16 / 100 : ℝ) 2 := ⟨hc.1, hc.2.trans sourcePrincipalZetaLine_mem.2⟩
    have h0 := sourceContourHeightWeight_nonneg y
    have he : Real.exp (-((u+y)^2)) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _))
    exact (hbound hX hY hZ σ₁ le_rfl c hc' u y hy).trans
      (mul_le_mul (mul_le_mul_of_nonneg_left (hscale σ₁ ⟨le_rfl,sourcePrincipalSigma_le_four⟩
        1 (by norm_num) c hc') hC) (mul_le_of_le_one_right h0 he)
        (mul_nonneg h0 (Real.exp_nonneg _)) (mul_nonneg hC hB))
  have hK (z : ℂ) (_ : (16 / 100 : ℝ) ≤ z.re) (_ : z.re ≤ z₁) (hz : z ≠ (1 / 6 : ℂ)) :
      K z = A z / (z - 1 / 6) := by
    dsimp only [A, K]
    rw [sourcePrincipalPoissonZRegularized_eq F hζ S₀ η v X Y Z ξ z hz]
    exact (eq_div_iff (sub_ne_zero.mpr hz)).mpr (mul_comm _ _)
  have hL (y : ℝ) : δ ≤ ‖(6 : ℂ) * sourcePoissonVertical (16 / 100) y - 1‖ :=
    (by norm_num [δ] : δ ≤ |6 * (16 / 100 : ℝ) - 1|).trans (sourcePrincipalVertical_z_gap_re _ _)
  have hR (y : ℝ) : δ ≤ ‖(6 : ℂ) * sourcePoissonVertical z₁ y - 1‖ :=
    (by norm_num [δ, sourcePrincipalZetaLine] : δ ≤ |6 * z₁ - 1|).trans (sourcePrincipalVertical_z_gap_re _ _)
  have hs := source_verticalIntegral_simple_pole_of_heightWeight A K (p := 1 / 6)
    (by norm_num : (16 / 100 : ℝ) < 1 / 6) sourcePrincipalZetaLine_gt_sixth hA
    (by simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using hK)
    (fun y => hslice _ ⟨le_rfl,hab⟩ y (hL y))
    (fun y => hslice _ ⟨hab,le_rfl⟩ y (hR y))
    (fun c hc y hy => hslice c hc y
      ((by dsimp [δ]; linarith only [hy] : δ ≤ 6 * |y|).trans (sourcePrincipalVertical_z_gap_im c y)))
  simpa only [A, K, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using hs

end
end ArtinMatthews.SourceEulerAssembly
