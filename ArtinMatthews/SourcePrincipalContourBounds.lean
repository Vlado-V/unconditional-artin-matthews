module

public import ArtinMatthews.SourcePrincipalContourAnalytic
public import ArtinMatthews.SourceContourHeightWeight
public import ArtinMatthews.SourceExteriorZetaBounds
public import ArtinMatthews.SourceSLocalProbeVertical
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! Polynomial Dedekind growth and actual rapid weights on the principal strips. -/

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain Set
open VaryingKummerAnalytic QuadraticWeil SourcePhysical
open scoped NumberField Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F]

private theorem weightedZeta_height_bound (T : Finset (ProbePrime F))
    (scale l r δ : ℝ) (hscale : 1 ≤ scale) (hl : 0 ≤ l) (hδ : 0 < δ) (G : ℂ → ℂ)
    (hrapid : ∀ n : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℂ, l ≤ s.re → s.re ≤ r →
      (1 + |s.im|) ^ n * ‖G s‖ ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Icc l r, ∀ t : ℝ,
      δ ≤ ‖(scale : ℂ) * sourcePoissonVertical x t - 1‖ →
      ‖G (sourcePoissonVertical x t) * principalExteriorZeta T ((scale : ℂ) * sourcePoissonVertical x t)‖ ≤
        C * sourceContourHeightWeight t := by
  obtain ⟨A, m, hA, hzeta⟩ := exists_sourceExteriorZeta_height_bound_away_pole F T
  obtain ⟨B, hB, hweight⟩ := hrapid (m + 2)
  let D := (A / δ + sourceRayAbsoluteEulerBound F (5 / 4)) * (2 : ℝ) ^ T.card
  have hD : 0 ≤ D := by
    dsimp [D]
    exact mul_nonneg (add_nonneg (div_nonneg hA.le hδ.le) (sourceRayAbsoluteEulerBound_pos F _).le)
      (by positivity)
  have hscale0 : 0 ≤ scale := zero_le_one.trans hscale
  refine ⟨D * scale ^ m * ((2 : ℝ) ^ m * B), by positivity, fun x hx t hp => ?_⟩
  let z := sourcePoissonVertical x t
  have hRe : ((scale : ℂ) * z).re = scale * x := by simp [z, Complex.mul_re]
  have hIm : ((scale : ℂ) * z).im = scale * t := by simp [z, Complex.mul_im]
  have hζ := hzeta δ hδ ((scale : ℂ) * z) (by rw [hRe]; exact mul_nonneg hscale0 (hl.trans hx.1)) hp
  rw [hIm, abs_mul, abs_of_nonneg hscale0] at hζ
  change ‖principalExteriorZeta T ((scale : ℂ) * z)‖ ≤ D * (scale * |t| + 2) ^ m at hζ
  have hpw : (scale * |t| + 2) ^ m ≤ scale ^ m * (|t| + 2) ^ m := by
    rw [← mul_pow, mul_add]
    apply pow_le_pow_left₀ (by positivity) _ m
    linarith
  have hG := sourceContourHeightWeight_of_rapid m t B ‖G z‖ (norm_nonneg _)
    (by simpa [z] using hweight z (by simpa [z] using hx.1) (by simpa [z] using hx.2))
  rw [norm_mul]
  calc
    _ ≤ ‖G z‖ * (D * (scale * |t| + 2) ^ m) := mul_le_mul_of_nonneg_left hζ (norm_nonneg _)
    _ ≤ ‖G z‖ * (D * (scale ^ m * (|t| + 2) ^ m)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpw hD) (norm_nonneg _)
    _ = (D * scale ^ m) * ((|t| + 2) ^ m * ‖G z‖) := by ring
    _ ≤ (D * scale ^ m) * (((2 : ℝ) ^ m * B) * sourceContourHeightWeight t) :=
      mul_le_mul_of_nonneg_left hG (mul_nonneg hD (pow_nonneg hscale0 _))
    _ = _ := by ring

variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
variable {J : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F J)
variable (v : InfinitePlace F)
local notation "S" => sourceHilbertSet F S₀
local notation "M̂" => sourceSLocalProbeMellin F hζ S v
local notation "Ŵ" => sourceProbeW1Mellin
local notation "H" => sourceContourHeightWeight

theorem sourcePrincipalPoissonWFactor_height_bound (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b ∈ Icc (95 / 100 : ℝ) 4, ∀ t : ℝ,
      δ ≤ ‖sourcePoissonVertical b t - 1‖ →
      ‖Ŵ (sourcePoissonVertical b t) * principalExteriorZeta S (sourcePoissonVertical b t)‖ ≤ C * H t := by
  simpa only [Complex.ofReal_one, one_mul] using
    weightedZeta_height_bound F S 1 (95 / 100) 4 δ le_rfl (by norm_num) hδ Ŵ
      (fun n => by
        obtain ⟨B, hB, h⟩ := sourceProbeW1Mellin_strip_decay (95 / 100) 4 n
        exact ⟨B, hB.le, h⟩)

theorem sourcePrincipalPoissonZFactor_height_bound (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c ∈ Icc (16 / 100 : ℝ) 2, ∀ y : ℝ,
      δ ≤ ‖(6 : ℂ) * sourcePoissonVertical c y - 1‖ →
      ‖M̂ (sourcePoissonVertical c y) * principalExteriorZeta S (6 * sourcePoissonVertical c y)‖ ≤ C * H y := by
  simpa only [Complex.ofReal_ofNat] using
    weightedZeta_height_bound F S 6 (16 / 100) 2 δ (by norm_num) (by norm_num) hδ M̂
      (fun n => sourceSLocalProbeMellin_vertical_rapid F hζ S v n (16 / 100) 2 (by norm_num))

theorem sourcePrincipalPoissonKernel_vertical_norm {X Y Z : ℝ}
    (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) (a b c u t y : ℝ) :
    let ξ := sourcePoissonVertical a u
    let w := sourcePoissonVertical b t
    let z := sourcePoissonVertical c y
    ‖sourcePrincipalPoissonKernel F hζ S₀ η v X Y Z (ξ, w, z)‖ =
      sourcePoissonTripleScale X Y Z a b c * (‖sourcePrincipalEulerAmplitude F hζ S₀ η (ξ, w, z)‖ *
        (‖Ŵ w * principalExteriorZeta S w‖ * ‖M̂ z * principalExteriorZeta S (6 * z)‖ *
          Real.exp (-((u + y) ^ 2)))) := by
  let A (p : SourcePoissonHeights) := sourcePrincipalEulerExtension F hζ S₀ η
    (sourcePoissonVertical a p.2, sourcePoissonVertical b p.1.1, sourcePoissonVertical c p.1.2)
  let p : SourcePoissonHeights := ((t, y), u)
  have h := sourcePoissonTripleKernel_norm hX hY hZ a b c
    (fun t => Ŵ (sourcePoissonVertical b t)) (fun y => M̂ (sourcePoissonVertical c y)) A p
  dsimp only [A, p] at h
  change ‖sourcePrincipalPoissonKernel F hζ S₀ η v X Y Z
    (sourcePoissonVertical a u, sourcePoissonVertical b t, sourcePoissonVertical c y)‖ = _ at h
  dsimp only
  rw [h, sourcePrincipalEulerExtension]
  simp only [norm_mul]
  ring

theorem sourcePrincipalPoissonWResidue_vertical_norm {X Y Z : ℝ}
    (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) (a c u y : ℝ) :
    let ξ := sourcePoissonVertical a u
    let z := sourcePoissonVertical c y
    ‖sourcePrincipalPoissonWResidue F hζ S₀ η v X Y Z ξ z‖ =
      sourcePoissonTripleScale X Y Z a 1 c *
        (‖sourcePrincipalEulerAmplitude F hζ S₀ η (ξ, 1, z)‖ *
          (‖principalExteriorZetaResidue F S‖ * ‖M̂ z * principalExteriorZeta S (6 * z)‖ *
            Real.exp (-((u + y) ^ 2)))) := by
  let A (p : SourcePoissonHeights) := principalExteriorZeta S (6 * sourcePoissonVertical c p.1.2) *
    principalExteriorZetaResidue F S * sourcePrincipalEulerAmplitude F hζ S₀ η
      (sourcePoissonVertical a p.2, 1, sourcePoissonVertical c p.1.2)
  let p : SourcePoissonHeights := ((0, y), u)
  have h := sourcePoissonTripleKernel_norm hX hY hZ a 1 c
    (fun t => Ŵ (sourcePoissonVertical 1 t)) (fun y => M̂ (sourcePoissonVertical c y)) A p
  have h1 : sourcePoissonVertical 1 0 = 1 := by simp [sourcePoissonVertical]
  simp only [p, A, h1, sourceProbeW1Mellin_one, norm_one, one_mul] at h
  have he :
      sourcePoissonTripleKernel X Y Z a 1 c
        (fun t => Ŵ (sourcePoissonVertical 1 t)) (fun y => M̂ (sourcePoissonVertical c y)) A p =
      sourcePrincipalPoissonWResidue F hζ S₀ η v X Y Z (sourcePoissonVertical a u) (sourcePoissonVertical c y) := by
    simp only [sourcePoissonTripleKernel, p, A, h1, sourcePrincipalPoissonWResidue, sourcePrincipalPoissonWeight]
  rw [he] at h
  dsimp only
  rw [h]
  simp only [norm_mul]
  ring

theorem sourcePrincipalPoissonKernel_height_bound
    (hcut : principalAngularCutoff F J ⊆ S) (δw δz : ℝ) (hδw : 0 < δw) (hδz : 0 < δz) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {X Y Z : ℝ}, 0 < X → 0 < Y → 0 < Z →
      ∀ a : ℝ, sourcePrincipalSigma ≤ a → ∀ b ∈ Icc (95 / 100 : ℝ) 4,
      ∀ c ∈ Icc (16 / 100 : ℝ) 2, ∀ u t y : ℝ,
      δw ≤ ‖sourcePoissonVertical b t - 1‖ → δz ≤ ‖(6 : ℂ) * sourcePoissonVertical c y - 1‖ →
      ‖sourcePrincipalPoissonKernel F hζ S₀ η v X Y Z
        (sourcePoissonVertical a u, sourcePoissonVertical b t, sourcePoissonVertical c y)‖ ≤
        (C * sourcePoissonTripleScale X Y Z a b c) * ((H t * H y) * Real.exp (-((u + y) ^ 2))) := by
  obtain ⟨B, hB, hb⟩ := sourcePrincipalPoissonWFactor_height_bound F S₀ δw hδw
  obtain ⟨D, hD, hd⟩ := sourcePrincipalPoissonZFactor_height_bound F hζ S₀ v δz hδz
  let A := probeGoodProductUniformBound F * (sourceRayAbsoluteEulerBound F sourcePrincipalSigma * (4 : ℝ) ^ (S).card)
  have hA : 0 ≤ A := mul_nonneg (probeGoodProductUniformBound_pos F).le
    (mul_nonneg (sourceRayAbsoluteEulerBound_pos F _).le (by positivity))
  refine ⟨A * B * D, by positivity, ?_⟩
  intro X Y Z hX hY hZ a ha b hb' c hc u t y hw hz
  let q := (sourcePoissonVertical a u, sourcePoissonVertical b t, sourcePoissonVertical c y)
  have hq : q ∈ sourcePrincipalContourDomain := sourcePrincipalContourDomain_vertical ha hb'.1 hc.1 u t y
  have hAmp : ‖sourcePrincipalEulerAmplitude F hζ S₀ η q‖ ≤ A :=
    sourcePrincipalEulerAmplitude_norm_le F hζ S₀ η hcut (by norm_num [sourcePrincipalSigma])
      (by simpa [q] using ha) (interior_subset (probeEulerOpenDomain_subset_interior (sourcePrincipalContourDomain_subset_euler hq)))
  have hScale : 0 ≤ sourcePoissonTripleScale X Y Z a b c := by unfold sourcePoissonTripleScale; positivity
  have ht := sourceContourHeightWeight_nonneg t
  have hy := sourceContourHeightWeight_nonneg y
  rw [sourcePrincipalPoissonKernel_vertical_norm F hζ S₀ η v hX hY hZ]
  calc
    _ ≤ sourcePoissonTripleScale X Y Z a b c * (A * ((B * H t) * (D * H y) * Real.exp (-((u + y) ^ 2)))) := by
      gcongr
      · exact hb b hb' t hw
      · exact hd c hc y hz
    _ = _ := by ring

theorem sourcePrincipalPoissonWResidue_height_bound
    (hcut : principalAngularCutoff F J ⊆ S) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {X Y Z : ℝ}, 0 < X → 0 < Y → 0 < Z →
      ∀ a : ℝ, sourcePrincipalSigma ≤ a → ∀ c ∈ Icc (16 / 100 : ℝ) 2, ∀ u y : ℝ,
      δ ≤ ‖(6 : ℂ) * sourcePoissonVertical c y - 1‖ →
      ‖sourcePrincipalPoissonWResidue F hζ S₀ η v X Y Z (sourcePoissonVertical a u)
        (sourcePoissonVertical c y)‖ ≤
        (C * sourcePoissonTripleScale X Y Z a 1 c) * (H y * Real.exp (-((u + y) ^ 2))) := by
  obtain ⟨D, hD, hd⟩ := sourcePrincipalPoissonZFactor_height_bound F hζ S₀ v δ hδ
  let A := probeGoodProductUniformBound F * (sourceRayAbsoluteEulerBound F sourcePrincipalSigma * (4 : ℝ) ^ (S).card)
  have hA : 0 ≤ A := mul_nonneg (probeGoodProductUniformBound_pos F).le
    (mul_nonneg (sourceRayAbsoluteEulerBound_pos F _).le (by positivity))
  refine ⟨A * ‖principalExteriorZetaResidue F S‖ * D, by positivity, ?_⟩
  intro X Y Z hX hY hZ a ha c hc u y hz
  let q := (sourcePoissonVertical a u, (1 : ℂ), sourcePoissonVertical c y)
  have hq : q ∈ sourcePrincipalContourDomain := by
    simpa [q, sourcePoissonVertical] using sourcePrincipalContourDomain_vertical ha
      (by norm_num : (95 / 100 : ℝ) ≤ 1) hc.1 u 0 y
  have hAmp : ‖sourcePrincipalEulerAmplitude F hζ S₀ η q‖ ≤ A :=
    sourcePrincipalEulerAmplitude_norm_le F hζ S₀ η hcut (by norm_num [sourcePrincipalSigma])
      (by simpa [q] using ha) (interior_subset (probeEulerOpenDomain_subset_interior (sourcePrincipalContourDomain_subset_euler hq)))
  have hScale : 0 ≤ sourcePoissonTripleScale X Y Z a 1 c := by unfold sourcePoissonTripleScale; positivity
  have hy := sourceContourHeightWeight_nonneg y
  rw [sourcePrincipalPoissonWResidue_vertical_norm F hζ S₀ η v hX hY hZ]
  calc
    _ ≤ sourcePoissonTripleScale X Y Z a 1 c * (A * (‖principalExteriorZetaResidue F S‖ *
      (D * H y) * Real.exp (-((u + y) ^ 2)))) := by
        gcongr
        exact hd c hc y hz
    _ = _ := by ring

end
end ArtinMatthews.SourceEulerAssembly
