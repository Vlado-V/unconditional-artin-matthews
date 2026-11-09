module

public import ArtinMatthews.SourceKPArchRadialFlow
public import ArtinMatthews.SourceArchRadialMeasure
public import ArtinMatthews.SourceKPArchHyperbolicMeasure


set_option backward.privateInPublic true
@[expose] public section

/-! Exact product hyperbolic measure scaling for vertical dilation. -/
namespace ArtinMatthews
open NumberField Matrix Matrix.GeneralLinearGroup SourceArchJacquet MeasureTheory Set
open scoped NumberField MatrixGroups AdeleRing ENNReal NNReal
noncomputable section
variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

omit [NumberField K] in
theorem sourceKPArchRadialPoint_zero (p : SourceKPArchUpperHalfSpace K) :
    sourceKPArchRadialPoint K 0 p = p := by
  funext v
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    simp [sourceKPArchRadialPoint, sourceArchRadialPoint]

omit [NumberField K] in
theorem sourceKPArchRadialPoint_add (s t : ℝ) (p : SourceKPArchUpperHalfSpace K) :
    sourceKPArchRadialPoint K s (sourceKPArchRadialPoint K t p) =
      sourceKPArchRadialPoint K (s+t) p := by
  funext v
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    simp only [sourceKPArchRadialPoint, sourceArchRadialPoint, Real.exp_add]
    exact (mul_assoc _ _ _).symm

omit [NumberField K] in
theorem sourceKPArchRadialPoint_continuous (t : ℝ) :
    Continuous (sourceKPArchRadialPoint K t) := by
  apply continuous_pi
  intro v
  have hv : Continuous (fun p : SourceKPArchUpperHalfSpace K => p v) := _root_.continuous_apply v
  have hy : Continuous (fun p : SourceKPArchUpperHalfSpace K => (p v).2.val) :=
    (continuous_subtype_val.comp continuous_snd).comp hv
  exact (continuous_fst.comp hv).prodMk
    ((continuous_const.mul hy).subtype_mk _)

def sourceKPArchRadialPointHomeomorph (t : ℝ) :
    SourceKPArchUpperHalfSpace K ≃ₜ SourceKPArchUpperHalfSpace K where
  toFun := sourceKPArchRadialPoint K t
  invFun := sourceKPArchRadialPoint K (-t)
  left_inv p := by rw [sourceKPArchRadialPoint_add, neg_add_cancel, sourceKPArchRadialPoint_zero]
  right_inv p := by rw [sourceKPArchRadialPoint_add, add_neg_cancel, sourceKPArchRadialPoint_zero]
  continuous_toFun := sourceKPArchRadialPoint_continuous K t
  continuous_invFun := sourceKPArchRadialPoint_continuous K (-t)

theorem sourceKPArchRadialPoint_rationalBorel (t : ℝ) (γ : PGL(2,K))
    (hγ : γ ∈ sourceKPRationalBorel K) (p : SourceKPArchUpperHalfSpace K) :
    sourceKPArchRadialPoint K t (sourceKPArchUpperAction K hζ (sourceKPRationalArchMap K hζ γ) p) =
      sourceKPArchUpperAction K hζ (sourceKPRationalArchMap K hζ γ) (sourceKPArchRadialPoint K t p) := by
  have hmul (a q : PGL(2, InfiniteAdeleRing K)) :
      sourceKPArchGramCoordinates K hζ (a*q) =
        sourceKPArchUpperAction K hζ a (sourceKPArchGramCoordinates K hζ q) := by
    obtain ⟨a,rfl⟩ := ProjGenLinGroup.mk_surjective a
    obtain ⟨q,rfl⟩ := ProjGenLinGroup.mk_surjective q
    rw [← map_mul, sourceKPArchGramCoordinates_mk, sourceKPArchGramCoordinates_mk]
    exact sourceKPArchGramCoordinatesMatrix_mul K hζ a q
  let q := ProjGenLinGroup.mk (sourceKPArchUpperHalfSection K hζ p)
  have hq : sourceKPArchGramCoordinates K hζ q = p := sourceKPArchGramCoordinatesMatrix_section K hζ p
  calc
    _ = sourceKPArchRadialPoint K t
        (sourceKPArchGramCoordinates K hζ (sourceKPRationalArchMap K hζ γ*q)) := by rw [hmul, hq]
    _ = sourceKPArchGramCoordinates K hζ
        (sourceKPArchRadialFlow K hζ t (sourceKPRationalArchMap K hζ γ*q)) :=
      (sourceKPArchRadialFlow_coordinates K hζ t _).symm
    _ = sourceKPArchGramCoordinates K hζ
        (sourceKPRationalArchMap K hζ γ*sourceKPArchRadialFlow K hζ t q) := by
      rw [sourceKPArchRadialFlow_rationalBorel K hζ t γ hγ]
    _ = _ := by rw [hmul, sourceKPArchRadialFlow_coordinates, hq]

theorem sourceKPArchRadialPoint_map_hyperbolicMeasure (t : ℝ) :
    Measure.map (sourceKPArchRadialPoint K t) (sourceKPArchHyperbolicMeasure K) =
      ENNReal.ofReal (Real.exp (2*(Fintype.card (InfinitePlace K) : ℝ)*t)) •
        sourceKPArchHyperbolicMeasure K := by
  let c : ℝ≥0 := ⟨Real.exp (2*t), (Real.exp_pos _).le⟩
  have hc : ENNReal.ofReal (Real.exp (2*t)) = (c : ℝ≥0∞) := by
    change ENNReal.ofReal (c : ℝ) = (c : ℝ≥0∞)
    exact ENNReal.ofReal_coe_nnreal
  have : SigmaFinite ((c : ℝ≥0∞) • sourceArchHyperbolicMeasure) := by
    change SigmaFinite (c • sourceArchHyperbolicMeasure)
    infer_instance
  have : SigmaFinite
      (Measure.map (sourceArchRadialPoint t) sourceArchHyperbolicMeasure) := by
    rw [sourceArchRadialPoint_hyperbolicMeasure, hc]
    infer_instance
  have hpi : Measure.pi (fun _ : InfinitePlace K => (c : ℝ≥0∞) • sourceArchHyperbolicMeasure) =
      (c : ℝ≥0∞) ^ Fintype.card (InfinitePlace K) • sourceKPArchHyperbolicMeasure K := by
    apply Measure.pi_eq
    intro s _
    rw [Measure.smul_apply, sourceKPArchHyperbolicMeasure, Measure.pi_pi]
    simp only [Measure.smul_apply, smul_eq_mul, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_univ]
  change Measure.map (fun p v => sourceArchRadialPoint t (p v))
    (Measure.pi (fun _ : InfinitePlace K => sourceArchHyperbolicMeasure)) = _
  rw [Measure.pi_map_pi (fun _ => (sourceArchRadialPoint_measurable t).aemeasurable)]
  simp_rw [sourceArchRadialPoint_hyperbolicMeasure, hc]
  rw [hpi]
  congr 1
  rw [← hc, ← ENNReal.ofReal_pow (Real.exp_pos _).le]
  congr 1
  rw [← Real.exp_nat_mul]
  congr 1
  ring

theorem sourceKPArchRadialPoint_image_hyperbolicMeasure (t : ℝ)
    (A : Set (SourceKPArchUpperHalfSpace K)) (hA : MeasurableSet A) :
    sourceKPArchHyperbolicMeasure K (sourceKPArchRadialPoint K t '' A) =
      ENNReal.ofReal (Real.exp (-2*(Fintype.card (InfinitePlace K) : ℝ)*t)) *
        sourceKPArchHyperbolicMeasure K A := by
  have hp : sourceKPArchRadialPoint K (-t) ⁻¹' A = sourceKPArchRadialPoint K t '' A := by
    ext p
    constructor
    · intro h
      refine ⟨sourceKPArchRadialPoint K (-t) p, h, ?_⟩
      rw [sourceKPArchRadialPoint_add, add_neg_cancel, sourceKPArchRadialPoint_zero]
    · rintro ⟨p,hp,rfl⟩
      change sourceKPArchRadialPoint K (-t) (sourceKPArchRadialPoint K t p) ∈ A
      rw [sourceKPArchRadialPoint_add, neg_add_cancel, sourceKPArchRadialPoint_zero]
      exact hp
  have h := congrArg (fun ν : Measure (SourceKPArchUpperHalfSpace K) => ν A)
    (sourceKPArchRadialPoint_map_hyperbolicMeasure K (-t))
  rw [Measure.map_apply (sourceKPArchRadialPoint_continuous K (-t)).measurable hA,
    Measure.smul_apply, hp] at h
  have he : 2*(Fintype.card (InfinitePlace K) : ℝ)*(-t) =
      -2*(Fintype.card (InfinitePlace K) : ℝ)*t := by ring
  simpa only [he, smul_eq_mul] using h

end
end ArtinMatthews
