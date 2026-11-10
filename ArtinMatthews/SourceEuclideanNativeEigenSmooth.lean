module

public import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SchwartzGradient
public import ArtinMatthews.SourceEuclideanEigenNormalization
public import ArtinMatthews.SourceEuclideanEigenSobolev
public import ArtinMatthews.SourceEuclideanEllipticExtension
public import ArtinMatthews.SourceEuclideanSmoothGluing


set_option backward.privateInPublic true
@[expose] public section

/-! A locally smooth coercive native weak eigen-equation has actual
smooth representatives. Each chart uses the original coefficient and
forcing on its compactly localized weak tests. -/

namespace ArtinMatthews

open MeasureTheory Set Filter
open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison
open scoped SchwartzMap ContDiff Topology

noncomputable section

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]

local notation "J" => SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1)
local notation "grad" => EuclideanGradient.CM.Construction.sobolevVectorGradient
local notation "ordinary" => SchwartzGradient.CM.Construction.schwartzOrdinaryGradient
local notation "cF" => (2 * Real.pi * Complex.I : ℂ)
local notation "sF" => (‖(2 * Real.pi * Complex.I : ℂ)‖ ^ 2)

theorem sourceLocalEigen_smooth_near_point_of_native_tests
    (b : OrthonormalBasis ι ℝ E)
    (A : E → EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι) (d : E → ℂ)
    {U : Set E} (hU : IsOpen U) (hA : ContDiffOn ℝ ∞ A U) (hd : ContDiffOn ℝ ∞ d U)
    (hcomm : ∀ x ∈ U, ∀ w : EuclideanSpace ℂ ι, A x (cF • w) = cF • A x w)
    (u M : Lp ℂ 2 (volume : Measure E))
    (G : Lp (EuclideanSpace ℂ ι) 2 (volume : Measure E))
    (hM : J u = M) (hG : cF • grad b u = G)
    (hsol : ∀ g : 𝓢(E, ℂ), HasCompactSupport (g : E → ℂ) → tsupport g ⊆ U →
      (∫ x, inner ℝ (A x (G x)) (ordinary b g x)) = ∫ x, inner ℝ (d x • M x) (g x))
    {x : E} (hx : x ∈ U) {a : ℝ} (ha : 0 < a)
    (hpos : ∀ w : EuclideanSpace ℂ ι, a*‖w‖*‖w‖ ≤ inner ℝ (A x w) w) :
    ∃ W : Set E, IsOpen W ∧ x ∈ W ∧ W ⊆ U ∧
      ∃ v : BoundedContinuousFunction E ℂ, ContDiff ℝ (⊤ : ℕ∞) (v : E → ℂ) ∧
        (v : E → ℂ) =ᵐ[(volume : Measure E).restrict W] M := by
  let d' (y : E) := ((sF : ℝ) : ℂ)⁻¹ * d y
  have hd' : ContDiffOn ℝ ∞ d' U := contDiffOn_const.mul hd
  obtain ⟨V,hV,hxV,hVU,A',m,hAeq,hmeq,hA',hc,⟨L,hL⟩,⟨C,hC⟩,hpos'⟩ :=
    sourceElliptic_extension_at_point A d' hU hA hd' hx ha hpos
  have hweak := sourceLocalEigen_of_native_tests b A A' hA'.continuous hC hAeq
    (fun y hy => hcomm y (hVU hy)) u M G hM hG d m hmeq
    (fun g hgc hgV => hsol g hgc (hgV.trans hVU))
  obtain ⟨W,hW,hxW,hWV,v,hs,hv⟩ :=
    sourceLocalEigen_smooth_near_point b A' (A x) hA' hc hL hC (half_pos ha) hpos' hV u m hweak hxV
  exact ⟨W,hW,hxW,hWV.trans hVU,v,hs,by simpa only [hM] using hv⟩

theorem sourceLocalEigen_smooth_on_of_native_localization [SecondCountableTopology E]
    (b : OrthonormalBasis ι ℝ E)
    (A : E → EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι) (d f : E → ℂ)
    {U : Set E} (hU : IsOpen U) (hA : ContDiffOn ℝ ∞ A U) (hd : ContDiffOn ℝ ∞ d U)
    (hcomm : ∀ x ∈ U, ∀ w : EuclideanSpace ℂ ι, A x (cF • w) = cF • A x w)
    (hpos : ∀ x ∈ U, ∃ a > 0, ∀ w : EuclideanSpace ℂ ι, a*‖w‖*‖w‖ ≤ inner ℝ (A x w) w)
    (hlocal : ∀ x ∈ U, ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
      ∃ (u M : Lp ℂ 2 (volume : Measure E))
        (G : Lp (EuclideanSpace ℂ ι) 2 (volume : Measure E)),
        J u = M ∧ cF • grad b u = G ∧ (M : E → ℂ) =ᵐ[(volume : Measure E).restrict V] f ∧
        ∀ g : 𝓢(E, ℂ), HasCompactSupport (g : E → ℂ) → tsupport g ⊆ V →
          (∫ y, inner ℝ (A y (G y)) (ordinary b g y)) = ∫ y, inner ℝ (d y • M y) (g y)) :
    ∃ v : E → ℂ, ContDiffOn ℝ (⊤ : ℕ∞) v U ∧ v =ᵐ[(volume : Measure E).restrict U] f := by
  apply sourceSmoothRepresentative_glue volume hU f
  intro x hx
  obtain ⟨V,hV,hxV,hVU,u,M,G,hM,hG,hrep,hsol⟩ := hlocal x hx
  obtain ⟨a,ha,hax⟩ := hpos x hx
  obtain ⟨W,hW,hxW,hWV,v,hv,hva⟩ :=
    sourceLocalEigen_smooth_near_point_of_native_tests b A d hV (hA.mono hVU) (hd.mono hVU)
      (fun y hy => hcomm y (hVU hy)) u M G hM hG hsol hxV ha hax
  exact ⟨W,hW,hxW,hWV.trans hVU,v,hv.contDiffOn,hva.trans (ae_restrict_of_ae_restrict_of_subset hWV hrep)⟩

end
end ArtinMatthews
