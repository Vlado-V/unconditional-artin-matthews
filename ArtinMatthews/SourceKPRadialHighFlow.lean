module

public import ArtinMatthews.SourceKPHighCuspQuotient


set_option backward.privateInPublic true
@[expose] public section

/-! Changing-threshold radial homeomorphisms of the genuine full-frame high cusp. -/
namespace ArtinMatthews
open NumberField Matrix Topology
open scoped NumberField MatrixGroups AdeleRing
noncomputable section
variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPRadialHeightScale (t : ℝ) : ℝ :=
  Real.exp (2 * (Fintype.card (InfinitePlace K) : ℝ) * t)

include hζ in
theorem sourceKPRadialComplexCount :
    Fintype.card (InfinitePlace K) = InfinitePlace.nrComplexPlaces K := by
  have := source_isTotallyComplex K hζ
  rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    (NumberField.nrRealPlaces_eq_zero_iff (K := K)).mpr inferInstance, zero_add]

include hζ in
theorem sourceKPRadialHeightScale_eq_nrComplex (t : ℝ) :
    sourceKPRadialHeightScale K t =
      Real.exp (2 * (InfinitePlace.nrComplexPlaces K : ℝ) * t) := by
  rw [sourceKPRadialHeightScale, sourceKPRadialComplexCount K hζ]

theorem sourceKPRadialHeightScale_pos (t : ℝ) : 0 < sourceKPRadialHeightScale K t := Real.exp_pos _

theorem sourceKPRadialHeightScale_neg_mul (t : ℝ) :
    sourceKPRadialHeightScale K (-t) * sourceKPRadialHeightScale K t = 1 := by
  rw [sourceKPRadialHeightScale, sourceKPRadialHeightScale, ← Real.exp_add]
  have h : 2 * (Fintype.card (InfinitePlace K) : ℝ) * -t +
      2 * (Fintype.card (InfinitePlace K) : ℝ) * t = 0 := by ring
  rw [h, Real.exp_zero]

def sourceKPHighCuspRadialFinite (t T : ℝ) (x : SourceKPHighCuspFinite K hζ T) :
    SourceKPHighCuspFinite K hζ (sourceKPRadialHeightScale K t * T) :=
  ⟨sourceKPFiniteLevelRadialFlow K hζ t x.val, by
    rw [sourceKPFiniteLevelRadialFlow_height]
    exact mul_lt_mul_of_pos_left x.property (sourceKPRadialHeightScale_pos K t)⟩

def sourceKPHighCuspRadialFiniteInv (t T : ℝ)
    (x : SourceKPHighCuspFinite K hζ (sourceKPRadialHeightScale K t * T)) :
    SourceKPHighCuspFinite K hζ T :=
  ⟨sourceKPFiniteLevelRadialFlow K hζ (-t) x.val, by
    rw [sourceKPFiniteLevelRadialFlow_height]
    change T < sourceKPRadialHeightScale K (-t) * sourceKPFiniteLevelHeight K hζ x.val
    calc
      T = sourceKPRadialHeightScale K (-t) * (sourceKPRadialHeightScale K t * T) := by
        rw [← mul_assoc, sourceKPRadialHeightScale_neg_mul, one_mul]
      _ < _ := mul_lt_mul_of_pos_left x.property (sourceKPRadialHeightScale_pos K (-t))⟩

theorem sourceKPHighCuspRadialFinite_left_inv (t T : ℝ) (x : SourceKPHighCuspFinite K hζ T) :
    sourceKPHighCuspRadialFiniteInv K hζ t T (sourceKPHighCuspRadialFinite K hζ t T x) = x := by
  apply Subtype.ext
  change sourceKPFiniteLevelRadialFlow K hζ (-t) (sourceKPFiniteLevelRadialFlow K hζ t x.val) = x.val
  rw [sourceKPFiniteLevelRadialFlow_add, neg_add_cancel, sourceKPFiniteLevelRadialFlow_zero]

theorem sourceKPHighCuspRadialFinite_right_inv (t T : ℝ)
    (x : SourceKPHighCuspFinite K hζ (sourceKPRadialHeightScale K t * T)) :
    sourceKPHighCuspRadialFinite K hζ t T (sourceKPHighCuspRadialFiniteInv K hζ t T x) = x := by
  apply Subtype.ext
  change sourceKPFiniteLevelRadialFlow K hζ t (sourceKPFiniteLevelRadialFlow K hζ (-t) x.val) = x.val
  rw [sourceKPFiniteLevelRadialFlow_add, add_neg_cancel, sourceKPFiniteLevelRadialFlow_zero]

theorem sourceKPHighCuspRadialFinite_equivariant (t T : ℝ)
    (b : sourceKPRationalBorel K) (x : SourceKPHighCuspFinite K hζ T) :
    sourceKPHighCuspRadialFinite K hζ t T (b • x) = b • sourceKPHighCuspRadialFinite K hζ t T x :=
  Subtype.ext (sourceKPFiniteLevelRadialFlow_rationalBorel K hζ t b.val b.property x.val)

theorem sourceKPHighCuspRadialFiniteInv_equivariant (t T : ℝ)
    (b : sourceKPRationalBorel K)
    (x : SourceKPHighCuspFinite K hζ (sourceKPRadialHeightScale K t * T)) :
    sourceKPHighCuspRadialFiniteInv K hζ t T (b • x) = b • sourceKPHighCuspRadialFiniteInv K hζ t T x :=
  Subtype.ext (sourceKPFiniteLevelRadialFlow_rationalBorel K hζ (-t) b.val b.property x.val)

def sourceKPHighCuspRadialBorel (t T : ℝ) :
    SourceKPHighCuspBorelQuotient K hζ T →
      SourceKPHighCuspBorelQuotient K hζ (sourceKPRadialHeightScale K t * T) :=
  Quotient.map (sourceKPHighCuspRadialFinite K hζ t T) (by
    intro x y hxy
    obtain ⟨b,hb⟩ := MulAction.mem_orbit_iff.mp hxy
    apply MulAction.mem_orbit_iff.mpr
    exact ⟨b, by rw [← sourceKPHighCuspRadialFinite_equivariant, hb]⟩)

def sourceKPHighCuspRadialBorelInv (t T : ℝ) :
    SourceKPHighCuspBorelQuotient K hζ (sourceKPRadialHeightScale K t * T) →
      SourceKPHighCuspBorelQuotient K hζ T :=
  Quotient.map (sourceKPHighCuspRadialFiniteInv K hζ t T) (by
    intro x y hxy
    obtain ⟨b,hb⟩ := MulAction.mem_orbit_iff.mp hxy
    apply MulAction.mem_orbit_iff.mpr
    exact ⟨b, by rw [← sourceKPHighCuspRadialFiniteInv_equivariant, hb]⟩)

theorem sourceKPHighCuspRadialBorel_mk (t T : ℝ) (x : SourceKPHighCuspFinite K hζ T) :
    sourceKPHighCuspRadialBorel K hζ t T (Quotient.mk _ x) =
      Quotient.mk _ (sourceKPHighCuspRadialFinite K hζ t T x) := rfl

theorem sourceKPHighCuspRadialBorelInv_mk (t T : ℝ)
    (x : SourceKPHighCuspFinite K hζ (sourceKPRadialHeightScale K t*T)) :
    sourceKPHighCuspRadialBorelInv K hζ t T (Quotient.mk _ x) =
      Quotient.mk _ (sourceKPHighCuspRadialFiniteInv K hζ t T x) := rfl

theorem sourceKPHighCuspRadialFinite_continuous (t T : ℝ) :
    Continuous (sourceKPHighCuspRadialFinite K hζ t T) := by
  have harg : Continuous (fun x : SourceKPHighCuspFinite K hζ T => (t,x.val)) :=
    continuous_const.prodMk continuous_subtype_val
  have h := (sourceKPFiniteLevelRadialFlow_continuous K hζ).comp harg
  exact h.subtype_mk (fun x => (sourceKPHighCuspRadialFinite K hζ t T x).property)

theorem sourceKPHighCuspRadialFiniteInv_continuous (t T : ℝ) :
    Continuous (sourceKPHighCuspRadialFiniteInv K hζ t T) := by
  have harg : Continuous (fun x : SourceKPHighCuspFinite K hζ (sourceKPRadialHeightScale K t*T) =>
      (-t,x.val)) := continuous_const.prodMk continuous_subtype_val
  have h := (sourceKPFiniteLevelRadialFlow_continuous K hζ).comp harg
  exact h.subtype_mk (fun x => (sourceKPHighCuspRadialFiniteInv K hζ t T x).property)

theorem sourceKPHighCuspRadialBorel_continuous (t T : ℝ) :
    Continuous (sourceKPHighCuspRadialBorel K hζ t T) := by
  apply isQuotientMap_quotient_mk'.continuous_iff.mpr
  have hmk : Continuous (Quotient.mk (MulAction.orbitRel (sourceKPRationalBorel K)
      (SourceKPHighCuspFinite K hζ (sourceKPRadialHeightScale K t*T)))) := continuous_quotient_mk'
  change Continuous (fun x : SourceKPHighCuspFinite K hζ T =>
    sourceKPHighCuspRadialBorel K hζ t T (Quotient.mk _ x))
  simpa only [Function.comp_def, sourceKPHighCuspRadialBorel_mk] using
    hmk.comp (sourceKPHighCuspRadialFinite_continuous K hζ t T)

theorem sourceKPHighCuspRadialBorelInv_continuous (t T : ℝ) :
    Continuous (sourceKPHighCuspRadialBorelInv K hζ t T) := by
  apply isQuotientMap_quotient_mk'.continuous_iff.mpr
  have hmk : Continuous (Quotient.mk (MulAction.orbitRel (sourceKPRationalBorel K)
      (SourceKPHighCuspFinite K hζ T))) := continuous_quotient_mk'
  change Continuous (fun x : SourceKPHighCuspFinite K hζ (sourceKPRadialHeightScale K t*T) =>
    sourceKPHighCuspRadialBorelInv K hζ t T (Quotient.mk _ x))
  simpa only [Function.comp_def, sourceKPHighCuspRadialBorelInv_mk] using
    hmk.comp (sourceKPHighCuspRadialFiniteInv_continuous K hζ t T)

def sourceKPHighCuspRadialBorelHomeomorph (t T : ℝ) :
    SourceKPHighCuspBorelQuotient K hζ T ≃ₜ
      SourceKPHighCuspBorelQuotient K hζ (sourceKPRadialHeightScale K t * T) where
  toFun := sourceKPHighCuspRadialBorel K hζ t T
  invFun := sourceKPHighCuspRadialBorelInv K hζ t T
  left_inv q := by
    induction q using Quotient.inductionOn with
    | _ x =>
      change Quotient.mk _ (sourceKPHighCuspRadialFiniteInv K hζ t T
        (sourceKPHighCuspRadialFinite K hζ t T x)) = Quotient.mk _ x
      rw [sourceKPHighCuspRadialFinite_left_inv]
  right_inv q := by
    induction q using Quotient.inductionOn with
    | _ x =>
      change Quotient.mk _ (sourceKPHighCuspRadialFinite K hζ t T
        (sourceKPHighCuspRadialFiniteInv K hζ t T x)) = Quotient.mk _ x
      rw [sourceKPHighCuspRadialFinite_right_inv]
  continuous_toFun := sourceKPHighCuspRadialBorel_continuous K hζ t T
  continuous_invFun := sourceKPHighCuspRadialBorelInv_continuous K hζ t T

def sourceKPHighCuspRadialHomeomorph (t T : ℝ) (hT : 1 < T)
    (htT : 1 < sourceKPRadialHeightScale K t * T) :
    SourceKPHighCuspAutomorphic K hζ T ≃ₜ
      SourceKPHighCuspAutomorphic K hζ (sourceKPRadialHeightScale K t * T) :=
  (sourceKPHighCuspHomeomorph K hζ T hT).symm.trans
    ((sourceKPHighCuspRadialBorelHomeomorph K hζ t T).trans
      (sourceKPHighCuspHomeomorph K hζ _ htT))

theorem sourceKPHighCuspHomeomorph_mk (T : ℝ) (hT : 1 < T) (x : SourceKPHighCuspFinite K hζ T) :
    sourceKPHighCuspHomeomorph K hζ T hT (Quotient.mk _ x) = sourceKPHighCuspProjection K hζ T x := rfl

theorem sourceKPHighCuspRadialHomeomorph_rep (t T : ℝ) (hT : 1 < T)
    (htT : 1 < sourceKPRadialHeightScale K t * T) (x : SourceKPHighCuspFinite K hζ T) :
    sourceKPHighCuspRadialHomeomorph K hζ t T hT htT (sourceKPHighCuspProjection K hζ T x) =
      sourceKPHighCuspProjection K hζ _ (sourceKPHighCuspRadialFinite K hζ t T x) := by
  change sourceKPHighCuspHomeomorph K hζ _ htT
    (sourceKPHighCuspRadialBorel K hζ t T
      ((sourceKPHighCuspHomeomorph K hζ T hT).symm (sourceKPHighCuspProjection K hζ T x))) = _
  rw [← sourceKPHighCuspHomeomorph_mk K hζ T hT x, Homeomorph.symm_apply_apply]
  rfl

theorem sourceKPHighCuspRadialHomeomorph_height (t T : ℝ) (hT : 1 < T)
    (htT : 1 < sourceKPRadialHeightScale K t * T) (q : SourceKPHighCuspAutomorphic K hζ T) :
    sourceKPAutomorphicOrbitHeight K hζ (sourceKPHighCuspRadialHomeomorph K hζ t T hT htT q).val =
      sourceKPRadialHeightScale K t * sourceKPAutomorphicOrbitHeight K hζ q.val := by
  obtain ⟨q,rfl⟩ := sourceKPHighCuspQuotientMap_surjective K hζ T q
  induction q using Quotient.inductionOn with
  | _ x =>
    rw [sourceKPHighCuspQuotientMap_mk, sourceKPHighCuspRadialHomeomorph_rep]
    change sourceKPFiniteLevelOrbitHeight K hζ
      (sourceKPFiniteLevelRadialFlow K hζ t x.val) =
        sourceKPRadialHeightScale K t * sourceKPFiniteLevelOrbitHeight K hζ x.val
    have hout : 1 < sourceKPFiniteLevelHeight K hζ (sourceKPFiniteLevelRadialFlow K hζ t x.val) :=
      htT.trans (sourceKPHighCuspRadialFinite K hζ t T x).property
    rw [sourceKPFiniteLevelOrbitHeight_eq_height_of_high K hζ
      (sourceKPFiniteLevelRadialFlow K hζ t x.val) hout,
      sourceKPFiniteLevelOrbitHeight_eq_height_of_high K hζ x.val (hT.trans x.property),
      sourceKPFiniteLevelRadialFlow_height]
    rfl

def sourceKPHighCuspRadialBorelValue (t T : ℝ)
    (q : SourceKPHighCuspBorelQuotient K hζ T) : SourceKPAutomorphicLevel K hζ :=
  Quotient.liftOn q (fun x : SourceKPHighCuspFinite K hζ T =>
    Quotient.mk _ (sourceKPFiniteLevelRadialFlow K hζ t x.val)) (by
      intro x y hxy
      obtain ⟨b,hb⟩ := MulAction.mem_orbit_iff.mp hxy
      apply Quotient.sound
      apply MulAction.mem_orbit_iff.mpr
      refine ⟨b.val, ?_⟩
      have hb' : b.val • y.val = x.val := congrArg Subtype.val hb
      rw [← sourceKPFiniteLevelRadialFlow_rationalBorel K hζ t b.val b.property, hb'])

def sourceKPHighCuspRadialValue (t T : ℝ) (hT : 1 < T)
    (q : SourceKPHighCuspAutomorphic K hζ T) : SourceKPAutomorphicLevel K hζ :=
  sourceKPHighCuspRadialBorelValue K hζ t T ((sourceKPHighCuspHomeomorph K hζ T hT).symm q)

theorem sourceKPHighCuspRadialBorelValue_continuous (T : ℝ) :
    Continuous (fun p : ℝ × SourceKPHighCuspBorelQuotient K hζ T =>
      sourceKPHighCuspRadialBorelValue K hζ p.1 T p.2) := by
  let π : ℝ × SourceKPHighCuspFinite K hζ T → ℝ × SourceKPHighCuspBorelQuotient K hζ T :=
    fun p => (p.1,Quotient.mk _ p.2)
  have hπc : Continuous π := continuous_fst.prodMk (continuous_quotient_mk'.comp continuous_snd)
  have hπo : IsOpenMap π := IsOpenMap.id.prodMap isOpenMap_quotient_mk'_mul
  have hπs : Function.Surjective π := by
    rintro ⟨t,q⟩
    obtain ⟨x,rfl⟩ := Quotient.mk_surjective q
    exact ⟨(t,x),rfl⟩
  have hπ := hπo.isQuotientMap hπc hπs
  apply hπ.continuous_iff.mpr
  have harg : Continuous (fun p : ℝ × SourceKPHighCuspFinite K hζ T => (p.1,p.2.val)) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have hflow := (sourceKPFiniteLevelRadialFlow_continuous K hζ).comp harg
  have hmk : Continuous (Quotient.mk (MulAction.orbitRel (PGL(2,K))
      (SourceKPFiniteLevelSpace K hζ))) := continuous_quotient_mk'
  exact hmk.comp hflow

theorem sourceKPHighCuspRadialValue_continuous (T : ℝ) (hT : 1 < T) :
    Continuous (fun p : ℝ × SourceKPHighCuspAutomorphic K hζ T =>
      sourceKPHighCuspRadialValue K hζ p.1 T hT p.2) := by
  have harg : Continuous (fun p : ℝ × SourceKPHighCuspAutomorphic K hζ T =>
      (p.1,(sourceKPHighCuspHomeomorph K hζ T hT).symm p.2)) :=
    continuous_fst.prodMk ((sourceKPHighCuspHomeomorph K hζ T hT).symm.continuous.comp continuous_snd)
  have h := (sourceKPHighCuspRadialBorelValue_continuous K hζ T).comp harg
  simpa only [Function.comp_def, sourceKPHighCuspRadialValue] using h

theorem sourceKPHighCuspRadialValue_rep (t T : ℝ) (hT : 1 < T)
    (x : SourceKPHighCuspFinite K hζ T) :
    sourceKPHighCuspRadialValue K hζ t T hT (sourceKPHighCuspProjection K hζ T x) =
      Quotient.mk _ (sourceKPFiniteLevelRadialFlow K hζ t x.val) := by
  unfold sourceKPHighCuspRadialValue
  rw [← sourceKPHighCuspHomeomorph_mk K hζ T hT x, Homeomorph.symm_apply_apply]
  rfl

theorem sourceKPHighCuspRadialValue_zero (T : ℝ) (hT : 1 < T)
    (q : SourceKPHighCuspAutomorphic K hζ T) : sourceKPHighCuspRadialValue K hζ 0 T hT q = q.val := by
  obtain ⟨q,rfl⟩ := sourceKPHighCuspQuotientMap_surjective K hζ T q
  induction q using Quotient.inductionOn with
  | _ x =>
    rw [sourceKPHighCuspQuotientMap_mk, sourceKPHighCuspRadialValue_rep,
      sourceKPFiniteLevelRadialFlow_zero]
    rfl

theorem sourceKPHighCuspRadialHomeomorph_value (t T : ℝ) (hT : 1 < T)
    (htT : 1 < sourceKPRadialHeightScale K t*T) (q : SourceKPHighCuspAutomorphic K hζ T) :
    (sourceKPHighCuspRadialHomeomorph K hζ t T hT htT q).val =
      sourceKPHighCuspRadialValue K hζ t T hT q := by
  obtain ⟨q,rfl⟩ := sourceKPHighCuspQuotientMap_surjective K hζ T q
  induction q using Quotient.inductionOn with
  | _ x =>
    rw [sourceKPHighCuspQuotientMap_mk, sourceKPHighCuspRadialHomeomorph_rep,
      sourceKPHighCuspRadialValue_rep]
    rfl

theorem sourceKPHighCuspRadialValue_add (s t T : ℝ) (hT : 1 < T)
    (htT : 1 < sourceKPRadialHeightScale K t*T) (q : SourceKPHighCuspAutomorphic K hζ T) :
    sourceKPHighCuspRadialValue K hζ s (sourceKPRadialHeightScale K t*T) htT
      (sourceKPHighCuspRadialHomeomorph K hζ t T hT htT q) =
      sourceKPHighCuspRadialValue K hζ (s+t) T hT q := by
  obtain ⟨q,rfl⟩ := sourceKPHighCuspQuotientMap_surjective K hζ T q
  induction q using Quotient.inductionOn with
  | _ x =>
    rw [sourceKPHighCuspQuotientMap_mk, sourceKPHighCuspRadialHomeomorph_rep,
      sourceKPHighCuspRadialValue_rep, sourceKPHighCuspRadialValue_rep]
    change (Quotient.mk _ (sourceKPFiniteLevelRadialFlow K hζ s
      (sourceKPFiniteLevelRadialFlow K hζ t x.val)) : SourceKPAutomorphicLevel K hζ) = _
    rw [sourceKPFiniteLevelRadialFlow_add]

end
end ArtinMatthews
