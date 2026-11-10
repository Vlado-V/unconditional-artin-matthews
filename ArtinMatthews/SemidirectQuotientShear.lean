module

public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Integral.Prod


set_option backward.privateInPublic true
@[expose] public section

/-! A measurable shear relates the product fundamental domain to its translated
fibers. This gives averaging over a normalized subgroup fundamental domain. -/
namespace ArtinMatthews
open MeasureTheory Set Function
open scoped ENNReal

noncomputable section

variable {L N G X : Type*} [Group L] [Group N] [Group G] [MulAction G X]
  [MulAction N X] [MeasurableSpace N] [MeasurableSpace X]
  (β : G →* MulAut L) (α : G →* MulAut N) (i : L →* N)
  (hi : ∀ g l, i (β g l) = α g (i l))

private def QuotientShearGroup (β : G →* MulAut L) (_α : G →* MulAut N)
    (_i : L →* N) (_hi : ∀ g l, _i (β g l) = _α g (_i l)) := L ⋊[β] G

local notation "H" => QuotientShearGroup β α i hi

local instance quotientShearGroupInst : Group H := inferInstanceAs (Group (L ⋊[β] G))

private abbrev quotientShearGroupData (g : H) : L ⋊[β] G := g

local instance quotientShearActionInst : MulAction H (N × X) where
  smul g p :=
    let b := quotientShearGroupData β α i hi g
    (i b.left * α b.right p.1, b.right • p.2)
  one_smul p := by
    apply Prod.ext
    · change i 1 * α 1 p.1 = p.1
      simp
    · exact one_smul G p.2
  mul_smul g h p := by
    let a := quotientShearGroupData β α i hi g
    let b := quotientShearGroupData β α i hi h
    apply Prod.ext
    · change i (a.left * β a.right b.left) * α (a.right * b.right) p.1 =
        i a.left * α a.right (i b.left * α b.right p.1)
      simp [hi, mul_assoc]
    · exact mul_smul a.right b.right p.2

variable (ν : Measure N) (μ : Measure X) [SFinite ν] [SFinite μ]
  (hAffine : ∀ (g : G) (l : L), MeasurePreserving (fun n => i l * α g n) ν ν)
  (hG : ∀ g : G, MeasurePreserving (fun x : X => g • x) μ μ)

omit [MulAction N X] in
include hAffine hG in
private theorem quotientShearAction_preserving (g : H) :
    MeasurePreserving (fun p : N × X => g • p) (ν.prod μ) (ν.prod μ) := by
  let b := quotientShearGroupData β α i hi g
  exact (hAffine b.right b.left).prod (hG b.right)

omit [MulAction N X] [SFinite ν] [SFinite μ] in
private theorem quotientShear_productDomain
    (D : Set N) (F : Set X) (hD : MeasurableSet D) (hF : MeasurableSet F)
    (hDN : ∀ n : N, ∃! l : L, i l * n ∈ D)
    (hFG : ∀ x : X, ∃! g : G, g • x ∈ F) :
    IsFundamentalDomain H (D ×ˢ F) (ν.prod μ) := by
  apply IsFundamentalDomain.mk' (hD.prod hF).nullMeasurableSet
  rintro ⟨n, x⟩
  obtain ⟨g, hg, hgu⟩ := hFG x
  obtain ⟨l, hl, hlu⟩ := hDN (α g n)
  refine ⟨(⟨l, g⟩ : L ⋊[β] G), ⟨hl, hg⟩, ?_⟩
  intro b hmem
  change L ⋊[β] G at b
  rcases b with ⟨l', g'⟩
  change i l' * α g' n ∈ D ∧ g' • x ∈ F at hmem
  have hg' := hgu g' hmem.2
  subst g'
  rw [hlu l' hmem.1]

variable (hN : ∀ n : N, MeasurePreserving (fun x : X => n • x) μ μ)
  (hjoint : Measurable (fun p : N × X => p.1 • p.2))
  (hinv : Measurable (fun n : N => n⁻¹))

private def quotientShear : (N × X) ≃ᵐ (N × X) where
  toFun p := (p.1, p.1 • p.2)
  invFun p := (p.1, p.1⁻¹ • p.2)
  left_inv p := Prod.ext rfl (inv_smul_smul p.1 p.2)
  right_inv p := Prod.ext rfl (smul_inv_smul p.1 p.2)
  measurable_toFun := measurable_fst.prodMk hjoint
  measurable_invFun := measurable_fst.prodMk
    (hjoint.comp ((hinv.comp measurable_fst).prodMk measurable_snd))

include hN in
private theorem quotientShear_preserving :
    MeasurePreserving (quotientShear hjoint hinv) (ν.prod μ) (ν.prod μ) :=
  (MeasurePreserving.id ν).skew_product hjoint
    (ae_of_all _ fun n => (hN n).map_eq)

variable (j : L →* G) (hj : ∀ l, α (j l) = 1)
  (hjAct : ∀ l (x : X), j l • x = i l • x)
  (hcompat : ∀ g n (x : X), g • (n • x) = α g n • (g • x))

private def quotientShearLabel : H ≃ H :=
  show (L ⋊[β] G) ≃ (L ⋊[β] G) from
  { toFun := fun g => ⟨g.left, (j g.left)⁻¹ * g.right⟩
    invFun := fun g => ⟨g.left, j g.left * g.right⟩
    left_inv := fun _ => SemidirectProduct.ext rfl (mul_inv_cancel_left _ _)
    right_inv := fun _ => SemidirectProduct.ext rfl (inv_mul_cancel_left _ _) }

include hj hjAct hcompat in
private theorem quotientShear_semiconj (g : H) :
    Semiconj (quotientShear hjoint hinv) (quotientShearLabel β α i hi j g • ·) (g • ·) := by
  rintro ⟨n, x⟩
  change L ⋊[β] G at g
  rcases g with ⟨l, g⟩
  have hscale : α ((j l)⁻¹ * g) = α g := by rw [map_mul, map_inv, hj, inv_one, one_mul]
  change (i l * α ((j l)⁻¹ * g) n, (i l * α ((j l)⁻¹ * g) n) • (((j l)⁻¹ * g) • x)) =
    (i l * α g n, g • (n • x))
  rw [hscale, hcompat, mul_smul, mul_smul]
  have hcancel : ∀ y : X, i l • ((j l)⁻¹ • y) = y := fun y => by
    rw [← hjAct, smul_inv_smul]
  have hcomm : ∀ y : X, (j l)⁻¹ • (α g n • y) = α g n • ((j l)⁻¹ • y) := fun y => by
    rw [hcompat, map_inv, hj, inv_one, MulAut.one_apply]
  rw [← hcomm, hcancel]

variable [Countable L] [Countable G]

include β α hi hAffine hG hN hjoint hinv j hj hjAct hcompat

/-- Average the fibers of an invariant function using the normalized measure of
the lattice domain. The domain in the transverse space is its actual quotient
fundamental domain, with the original measure. -/
theorem semidirectQuotient_average
    (D : Set N) (F : Set X) (hD : MeasurableSet D) (hF : MeasurableSet F)
    (hDN : ∀ n : N, ∃! l : L, i l * n ∈ D)
    (hFG : ∀ x : X, ∃! g : G, g • x ∈ F) (hmass : ν D = 1)
    (f : X → ℂ) (hfi : IntegrableOn f F μ)
    (hf : ∀ g : G, ∀ x : X, f (g • x) = f x) :
    Integrable (fun p : N × X => f (p.1 • p.2)) ((ν.restrict D).prod (μ.restrict F)) ∧
    (∫ x in F, f x ∂μ) = ∫ x in F, (∫ n in D, f (n • x) ∂ν) ∂μ := by
  let : Countable H := SemidirectProduct.equivProd.injective.countable
  let : MeasurableConstSMul H (N × X) :=
    ⟨fun g => (quotientShearAction_preserving β α i hi ν μ hAffine hG g).measurable⟩
  let : SMulInvariantMeasure H (N × X) (ν.prod μ) :=
    ⟨fun g s hs => (quotientShearAction_preserving β α i hi ν μ hAffine hG g).measure_preimage hs.nullMeasurableSet⟩
  let S := quotientShear hjoint hinv
  have hS := quotientShear_preserving ν μ hN hjoint hinv
  have hF₀ := quotientShear_productDomain β α i hi ν μ D F hD hF hDN hFG
  have hF₁ := hF₀.image_of_equiv S.toEquiv (hS.symm S).quasiMeasurePreserving
    (quotientShearLabel β α i hi j) (quotientShear_semiconj β α i hi hjoint hinv j hj hjAct hcompat)
  let f₀ : N × X → ℂ := fun p => f p.2
  have hInvariant (g : H) (p : N × X) : f₀ (g • p) = f₀ p :=
    hf (quotientShearGroupData β α i hi g).right p.2
  have hprob : IsProbabilityMeasure (ν.restrict D) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, hmass]⟩
  have h₀ : IntegrableOn f₀ (D ×ˢ F) (ν.prod μ) := by
    rw [IntegrableOn, ← Measure.prod_restrict]
    exact hfi.comp_snd (ν.restrict D)
  have h₁ := (hF₀.integrableOn_iff hF₁ hInvariant).mp h₀
  have hSr : MeasurePreserving S ((ν.prod μ).restrict (D ×ˢ F))
      ((ν.prod μ).restrict (S '' (D ×ˢ F))) :=
    hS.restrict_image_emb S.measurableEmbedding _
  have hSfi := hSr.integrable_comp_of_integrable h₁
  change Integrable (fun p : N × X => f (p.1 • p.2)) ((ν.prod μ).restrict (D ×ˢ F)) at hSfi
  rw [← Measure.prod_restrict] at hSfi
  have hSf := hSr.integral_comp S.measurableEmbedding f₀
  have hFub := integral_prod_symm (fun p : N × X => f (p.1 • p.2)) hSfi
  have hConst : (∫ p in D ×ˢ F, f₀ p ∂ν.prod μ) = ∫ x in F, f x ∂μ := by
    rw [← Measure.prod_restrict, integral_prod f₀ (hfi.comp_snd (ν.restrict D))]
    simp [f₀]
  refine ⟨hSfi, ?_⟩
  calc
    (∫ x in F, f x ∂μ) = ∫ p in D ×ˢ F, f₀ p ∂ν.prod μ := hConst.symm
    _ = ∫ p in S '' (D ×ˢ F), f₀ p ∂ν.prod μ :=
      hF₀.setIntegral_eq hF₁ hInvariant
    _ = ∫ p : N × X, f (p.1 • p.2) ∂(ν.restrict D).prod (μ.restrict F) := by
      rw [Measure.prod_restrict]
      exact hSf.symm
    _ = ∫ x in F, (∫ n in D, f (n • x) ∂ν) ∂μ := hFub

end
end ArtinMatthews
