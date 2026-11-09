module

public import ArtinMatthews.SourcePrincipalWeightedResidues
public import ArtinMatthews.SourceExteriorZetaBounds


set_option backward.privateInPublic true
@[expose] public section

/-! Holomorphy and the actual reciprocal bound on the principal contour region. -/

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators Set
open VaryingKummerAnalytic QuadraticWeil SourcePhysical
open scoped NumberField Classical
noncomputable section

def sourcePrincipalSigma : ℝ := 1 + 1 / 10000000
def sourcePrincipalZetaLine : ℝ := 1 / 6 + 1 / 10000000

def sourcePrincipalContourDomain : Set ProbeCoordinates :=
  {q | 1 < q.1.re ∧ 94999 / 100000 < q.2.1.re ∧ 15999 / 100000 < q.2.2.re}

def sourcePrincipalResidueDomain : Set (ℂ × ℂ) :=
  {q | 1 < q.1.re ∧ 15999 / 100000 < q.2.re}

theorem sourcePrincipalContourDomain_subset_euler :
    sourcePrincipalContourDomain ⊆ probeEulerOpenDomain := by
  rintro q ⟨hξ, hw, hz⟩
  exact Or.inr ⟨by linarith, hw, hz⟩

theorem sourcePrincipalContourDomain_vertical
    {a b c : ℝ} (ha : sourcePrincipalSigma ≤ a) (hb : 95 / 100 ≤ b) (hc : 16 / 100 ≤ c)
    (u t y : ℝ) :
    (sourcePoissonVertical a u, sourcePoissonVertical b t, sourcePoissonVertical c y) ∈
      sourcePrincipalContourDomain := by
  change 1 < (sourcePoissonVertical a u).re ∧
    94999 / 100000 < (sourcePoissonVertical b t).re ∧ 15999 / 100000 < (sourcePoissonVertical c y).re
  simp only [sourcePoissonVertical_re]
  unfold sourcePrincipalSigma at ha
  exact ⟨by linarith, by linarith, by linarith⟩

theorem sourcePrincipal_six_mul_ne_one {z : ℂ} (hz : z ≠ 1 / 6) : (6 : ℂ) * z ≠ 1 := by
  intro he
  apply hz
  linear_combination (1 / 6 : ℂ) * he

variable (F : Type) [Field F] [NumberField F]
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
variable {J : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F J)
variable (v : InfinitePlace F)
local notation "S" => sourceHilbertSet F S₀

theorem sourcePrincipalExteriorZeta_differentiableOn (T : Finset (ProbePrime F)) :
    DifferentiableOn ℂ (principalExteriorZeta T) {s : ℂ | s ≠ 1} := by
  intro s hs
  exact ((mixedDedekindZeta_analyticAt F hs).differentiableAt.mul
    ((principalZetaEulerFactor_entire T) s)).differentiableWithinAt

theorem sourcePrincipalExteriorL_inv_norm_le_right {a : ℝ} (ha : 1 < a)
    {s : ℂ} (hs : a ≤ s.re) :
    ‖(principalAngularExteriorL η S s)⁻¹‖ ≤ sourceRayAbsoluteEulerBound F a * (4 : ℝ) ^ (S).card := by
  rw [principalAngularExteriorL, mul_inv_rev, norm_mul, mul_comm]
  exact mul_le_mul (sourceRayDirichlet_norm_bounds F η ha hs).2
    (principalAngularRayEulerFactor_inv_norm_le η S (s := s) (by linarith)) (norm_nonneg _)
    (sourceRayAbsoluteEulerBound_pos F a).le

theorem sourcePrincipalEulerAmplitude_differentiableOn
    (hJ : J ≠ ⊥) (hcut : principalAngularCutoff F J ⊆ S) :
    DifferentiableOn ℂ (sourcePrincipalEulerAmplitude F hζ S₀ η) sourcePrincipalContourDomain := by
  have hC := (sourceGlobalCorrection_differentiableOn F hζ S₀ η hJ hcut 1 one_ne_zero).mono
    sourcePrincipalContourDomain_subset_euler
  have hL := (principalAngularExteriorL_differentiableOn η S).comp differentiableOn_fst
    (show MapsTo Prod.fst sourcePrincipalContourDomain {s : ℂ | 1 < s.re} from fun _ h => h.1)
  exact hC.mul (hL.inv (fun q hq => principalAngularExteriorL_ne_zero η S hq.1))

theorem sourcePrincipalEulerAmplitude_norm_le
    (hcut : principalAngularCutoff F J ⊆ S) {a : ℝ} (ha : 1 < a)
    {q : ProbeCoordinates} (hξ : a ≤ q.1.re) (hq : q ∈ probeEulerDomain) :
    ‖sourcePrincipalEulerAmplitude F hζ S₀ η q‖ ≤
      probeGoodProductUniformBound F * (sourceRayAbsoluteEulerBound F a * (4 : ℝ) ^ (S).card) := by
  let A := sourcePrimeRowCharacter F hζ S₀ 1 one_ne_zero
  let B := sourcePrimeRowTwist F hζ S₀ 1 one_ne_zero η
  let C := sourcePrimeRowThirdPhase F hζ S₀ 1 one_ne_zero η
  have ha' := sourceExteriorValues_norm_le_one F S₀ A
    (sourcePrimeRowCharacter_norm_le_one F hζ S₀ 1 one_ne_zero)
  have hb' := sourceExteriorValues_norm_le_one F S₀ B
    (sourcePrimeRowTwist_norm_le_one F hζ S₀ 1 one_ne_zero η)
  have hc' := sourceExteriorValues_norm_le_one F S₀ C
    (sourcePrimeRowThirdPhase_norm_le_one F hζ S₀ 1 one_ne_zero η)
  unfold sourcePrincipalEulerAmplitude
  rw [norm_mul, sourceGlobalCorrection, sourceElementExponents_one, Finsupp.support_zero,
    Finset.prod_empty, mul_one]
  exact mul_le_mul (probeEulerProduct_norm_le_uniform F S
    (probePrimeCutoff_subset_principalAngularCutoff.trans hcut) _ _ _ ha' hb' hc' hq)
    (sourcePrincipalExteriorL_inv_norm_le_right F S₀ η ha hξ) (norm_nonneg _)
    (probeGoodProductUniformBound_pos F).le

variable (hJ : J ≠ ⊥) (hcut : principalAngularCutoff F J ⊆ sourceHilbertSet F S₀)
variable {X Y Z : ℝ} (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {D : Set E}

include hJ hcut hX hY hZ in
theorem sourcePrincipalPoissonKernel_differentiableOn_path
    (p : E → ProbeCoordinates) (hp : DifferentiableOn ℂ p D)
    (hdom : MapsTo p D sourcePrincipalContourDomain)
    (hwp : ∀ x ∈ D, (p x).2.1 ≠ 1) (hzp : ∀ x ∈ D, (p x).2.2 ≠ 1 / 6) :
    DifferentiableOn ℂ (fun x => sourcePrincipalPoissonKernel F hζ S₀ η v X Y Z (p x)) D := by
  have hpos (x : E) (hx : x ∈ D) : 0 < (p x).2.2.re :=
    (by norm_num : (0 : ℝ) < 15999 / 100000).trans (hdom hx).2.2
  have hWgt := sourcePrincipalPoissonWeight_differentiableOn_path F hζ S₀ v hX hY hZ p hp hpos
  have hA := (sourcePrincipalEulerAmplitude_differentiableOn F hζ S₀ η hJ hcut).comp hp hdom
  have hw : DifferentiableOn ℂ (fun x => principalExteriorZeta S (p x).2.1) D :=
    (sourcePrincipalExteriorZeta_differentiableOn F S).comp hp.snd.fst hwp
  have h6 : DifferentiableOn ℂ (fun x => (6 : ℂ) * (p x).2.2) D :=
    (differentiableOn_const (6 : ℂ)).mul hp.snd.snd
  have hz : DifferentiableOn ℂ (fun x => principalExteriorZeta S (6 * (p x).2.2)) D :=
    (sourcePrincipalExteriorZeta_differentiableOn F S).comp h6
      (fun x hx => sourcePrincipal_six_mul_ne_one (hzp x hx))
  exact hWgt.mul ((hz.mul hw).mul hA)

include hJ hcut hX hY hZ in
theorem sourcePrincipalPoissonWRegularized_differentiableOn_path
    (p : E → ProbeCoordinates) (hp : DifferentiableOn ℂ p D)
    (hdom : MapsTo p D sourcePrincipalContourDomain) (hzp : ∀ x ∈ D, (p x).2.2 ≠ 1 / 6) :
    DifferentiableOn ℂ (fun x => sourcePrincipalPoissonWRegularized F hζ S₀ η v X Y Z (p x)) D := by
  have hpos (x : E) (hx : x ∈ D) : 0 < (p x).2.2.re :=
    (by norm_num : (0 : ℝ) < 15999 / 100000).trans (hdom hx).2.2
  have hWgt := sourcePrincipalPoissonWeight_differentiableOn_path F hζ S₀ v hX hY hZ p hp hpos
  have hA := (sourcePrincipalEulerAmplitude_differentiableOn F hζ S₀ η hJ hcut).comp hp hdom
  have hw : DifferentiableOn ℂ (fun x => principalExteriorZetaRegularized S (p x).2.1) D :=
    (principalExteriorZetaRegularized_entire S).differentiableOn.comp hp.snd.fst (mapsTo_univ _ _)
  have h6 : DifferentiableOn ℂ (fun x => (6 : ℂ) * (p x).2.2) D :=
    (differentiableOn_const (6 : ℂ)).mul hp.snd.snd
  have hz : DifferentiableOn ℂ (fun x => principalExteriorZeta S (6 * (p x).2.2)) D :=
    (sourcePrincipalExteriorZeta_differentiableOn F S).comp h6
      (fun x hx => sourcePrincipal_six_mul_ne_one (hzp x hx))
  exact hWgt.mul ((hz.mul hw).mul hA)

include hJ hcut hX hY hZ in
theorem sourcePrincipalPoissonWResidue_differentiableOn_path
    (q : E → ℂ × ℂ) (hq : DifferentiableOn ℂ q D)
    (hdom : MapsTo q D sourcePrincipalResidueDomain) (hzp : ∀ x ∈ D, (q x).2 ≠ 1 / 6) :
    DifferentiableOn ℂ (fun x => sourcePrincipalPoissonWResidue F hζ S₀ η v X Y Z (q x).1 (q x).2) D := by
  let p (x : E) := ((q x).1, (1 : ℂ), (q x).2)
  have hp : DifferentiableOn ℂ p D :=
    hq.fst.prodMk ((differentiableOn_const (1 : ℂ)).prodMk hq.snd)
  have hm : MapsTo p D sourcePrincipalContourDomain := fun x hx =>
    ⟨(hdom hx).1, by norm_num, (hdom hx).2⟩
  exact (sourcePrincipalPoissonWRegularized_differentiableOn_path F hζ S₀ η v hJ hcut hX hY hZ
    p hp hm hzp).congr (fun x _ =>
      (sourcePrincipalPoissonWRegularized_one F hζ S₀ η v X Y Z (q x).1 (q x).2).symm)

include hJ hcut hX hY hZ in
theorem sourcePrincipalPoissonZRegularized_differentiableOn_path
    (q : E → ℂ × ℂ) (hq : DifferentiableOn ℂ q D)
    (hdom : MapsTo q D sourcePrincipalResidueDomain) :
    DifferentiableOn ℂ (fun x => sourcePrincipalPoissonZRegularized F hζ S₀ η v X Y Z (q x).1 (q x).2) D := by
  let p (x : E) := ((q x).1, (1 : ℂ), (q x).2)
  have hp : DifferentiableOn ℂ p D :=
    hq.fst.prodMk ((differentiableOn_const (1 : ℂ)).prodMk hq.snd)
  have hm : MapsTo p D sourcePrincipalContourDomain := fun x hx =>
    ⟨(hdom hx).1, by norm_num, (hdom hx).2⟩
  have hWgt := sourcePrincipalPoissonWeight_differentiableOn_path F hζ S₀ v hX hY hZ p hp
    (fun x hx => (by norm_num : (0 : ℝ) < 15999 / 100000).trans (hdom hx).2)
  have hA := (sourcePrincipalEulerAmplitude_differentiableOn F hζ S₀ η hJ hcut).comp hp hm
  have hz : DifferentiableOn ℂ (fun x => principalExteriorZetaRegularized S (6 * (q x).2)) D :=
    (principalExteriorZetaRegularized_entire S).differentiableOn.comp
      (hq.snd.const_mul 6) (mapsTo_univ _ _)
  simp only [sourcePrincipalPoissonZRegularized, div_eq_mul_inv]
  exact hWgt.mul (((hz.mul (differentiableOn_const ((6 : ℂ)⁻¹))).mul
    (differentiableOn_const (principalExteriorZetaResidue F S))).mul hA)

end
end ArtinMatthews.SourceEulerAssembly
