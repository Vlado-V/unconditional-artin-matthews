module

public import ArtinMatthews.SourceArchRadialFlow
public import ArtinMatthews.SourceKPArchGramQuotient
public import ArtinMatthews.SourceAdelicOrbitHeightTopology
public import ArtinMatthews.SourceKPArchRightAction


set_option backward.privateInPublic true
@[expose] public section

/-! The actual infinite-adelic radial flow, with its finite coordinate retained. -/
namespace ArtinMatthews
open NumberField Matrix Matrix.GeneralLinearGroup SourceArchJacquet
open scoped NumberField MatrixGroups AdeleRing BigOperators
noncomputable section
variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPArchRadialPoint (t : ℝ) (p : SourceKPArchUpperHalfSpace K) :
    SourceKPArchUpperHalfSpace K := fun v => sourceArchRadialPoint t (p v)

def sourceKPArchRadialBorelMatrix (t : ℝ) (p : SourceKPArchUpperHalfSpace K) :
    GL (Fin 2) (InfiniteAdeleRing K) :=
  (sourceArchGLPiEquiv K).symm (fun v => (sourceKPArchMatrixComplexEquiv K hζ v).symm
    (sourceArchRadialBorel t (p v).1))

theorem sourceKPArchRadialBorelMatrix_at (t : ℝ) (p : SourceKPArchUpperHalfSpace K)
    (v : InfinitePlace K) :
    sourceKPArchMatrixComplexEquiv K hζ v
      (sourceArchGLPiEquiv K (sourceKPArchRadialBorelMatrix K hζ t p) v) =
        sourceArchRadialBorel t (p v).1 := by
  simp only [sourceKPArchRadialBorelMatrix, MulEquiv.apply_symm_apply]

def sourceKPArchRadialFlowMatrix (t : ℝ) (g : GL (Fin 2) (InfiniteAdeleRing K)) :
    GL (Fin 2) (InfiniteAdeleRing K) :=
  sourceKPArchRadialBorelMatrix K hζ t (sourceKPArchGramCoordinatesMatrix K hζ g) * g

theorem sourceKPArchRadialFlowMatrix_at (t : ℝ) (g : GL (Fin 2) (InfiniteAdeleRing K))
    (v : InfinitePlace K) :
    sourceKPArchMatrixComplexEquiv K hζ v
      (sourceArchGLPiEquiv K (sourceKPArchRadialFlowMatrix K hζ t g) v) =
        sourceArchRadialFlow t
          (sourceKPArchMatrixComplexEquiv K hζ v (sourceArchGLPiEquiv K g v)) := by
  simp only [sourceKPArchRadialFlowMatrix, map_mul, Pi.mul_apply,
    sourceKPArchRadialBorelMatrix_at, sourceKPArchGramCoordinatesMatrix,
    sourceArchGramCoordinates, sourceArchRadialFlow]

theorem sourceKPArchRadialFlowMatrix_coordinates (t : ℝ)
    (g : GL (Fin 2) (InfiniteAdeleRing K)) :
    sourceKPArchGramCoordinatesMatrix K hζ (sourceKPArchRadialFlowMatrix K hζ t g) =
      sourceKPArchRadialPoint K t (sourceKPArchGramCoordinatesMatrix K hζ g) := by
  funext v
  rw [sourceKPArchGramCoordinatesMatrix, sourceKPArchRadialFlowMatrix_at,
    sourceArchRadialFlow_coordinates]
  rfl

theorem sourceKPArchRadialFlowMatrix_zero (g : GL (Fin 2) (InfiniteAdeleRing K)) :
    sourceKPArchRadialFlowMatrix K hζ 0 g = g := by
  apply (sourceArchGLPiEquiv K).injective
  funext v
  apply (sourceKPArchMatrixComplexEquiv K hζ v).injective
  rw [sourceKPArchRadialFlowMatrix_at, sourceArchRadialFlow_zero]

theorem sourceKPArchRadialFlowMatrix_add (s t : ℝ)
    (g : GL (Fin 2) (InfiniteAdeleRing K)) :
    sourceKPArchRadialFlowMatrix K hζ s (sourceKPArchRadialFlowMatrix K hζ t g) =
      sourceKPArchRadialFlowMatrix K hζ (s+t) g := by
  apply (sourceArchGLPiEquiv K).injective
  funext v
  apply (sourceKPArchMatrixComplexEquiv K hζ v).injective
  rw [sourceKPArchRadialFlowMatrix_at, sourceKPArchRadialFlowMatrix_at,
    sourceKPArchRadialFlowMatrix_at, sourceArchRadialFlow_add]

theorem sourceKPArchNormalizedBorel_at (b : GL (Fin 2) (InfiniteAdeleRing K))
    (hb : b ∈ sourceKPRingNormalizedBorel (InfiniteAdeleRing K)) (v : InfinitePlace K) :
    sourceKPArchMatrixComplexEquiv K hζ v (sourceArchGLPiEquiv K b v) ∈
      sourceGL2NormalizedBorel ℂ := by
  constructor
  · change sourceKPArchComplexEquiv K hζ v (b 1 0 v) = 0
    rw [hb.1]
    exact map_zero _
  · change sourceKPArchComplexEquiv K hζ v (b 1 1 v) = 1
    rw [hb.2]
    exact map_one _

theorem sourceKPArchRadialFlowMatrix_borel (t : ℝ)
    (b g : GL (Fin 2) (InfiniteAdeleRing K))
    (hb : b ∈ sourceKPRingNormalizedBorel (InfiniteAdeleRing K)) :
    sourceKPArchRadialFlowMatrix K hζ t (b*g) = b*sourceKPArchRadialFlowMatrix K hζ t g := by
  apply (sourceArchGLPiEquiv K).injective
  funext v
  apply (sourceKPArchMatrixComplexEquiv K hζ v).injective
  rw [sourceKPArchRadialFlowMatrix_at, map_mul, Pi.mul_apply, map_mul,
    sourceArchRadialFlow_borel _ _ _ (sourceKPArchNormalizedBorel_at K hζ b hb v)]
  rw [map_mul, Pi.mul_apply, map_mul, sourceKPArchRadialFlowMatrix_at]

def sourceKPArchRadialFlow (t : ℝ) (q : PGL(2, InfiniteAdeleRing K)) :
    PGL(2, InfiniteAdeleRing K) :=
  ProjGenLinGroup.mk (sourceKPArchRadialBorelMatrix K hζ t (sourceKPArchGramCoordinates K hζ q)) * q

theorem sourceKPArchRadialFlow_mk (t : ℝ) (g : GL (Fin 2) (InfiniteAdeleRing K)) :
    sourceKPArchRadialFlow K hζ t (ProjGenLinGroup.mk g) =
      ProjGenLinGroup.mk (sourceKPArchRadialFlowMatrix K hζ t g) := by
  rw [sourceKPArchRadialFlow, sourceKPArchGramCoordinates_mk, ← map_mul]
  rfl

theorem sourceKPArchRadialFlow_zero (q : PGL(2, InfiniteAdeleRing K)) :
    sourceKPArchRadialFlow K hζ 0 q = q := by
  obtain ⟨g, rfl⟩ := ProjGenLinGroup.mk_surjective q
  rw [sourceKPArchRadialFlow_mk, sourceKPArchRadialFlowMatrix_zero]

theorem sourceKPArchRadialFlow_add (s t : ℝ) (q : PGL(2, InfiniteAdeleRing K)) :
    sourceKPArchRadialFlow K hζ s (sourceKPArchRadialFlow K hζ t q) =
      sourceKPArchRadialFlow K hζ (s+t) q := by
  obtain ⟨g, rfl⟩ := ProjGenLinGroup.mk_surjective q
  rw [sourceKPArchRadialFlow_mk, sourceKPArchRadialFlow_mk,
    sourceKPArchRadialFlowMatrix_add, sourceKPArchRadialFlow_mk]

theorem sourceKPArchRadialFlow_coordinates (t : ℝ) (q : PGL(2, InfiniteAdeleRing K)) :
    sourceKPArchGramCoordinates K hζ (sourceKPArchRadialFlow K hζ t q) =
      sourceKPArchRadialPoint K t (sourceKPArchGramCoordinates K hζ q) := by
  obtain ⟨g, rfl⟩ := ProjGenLinGroup.mk_surjective q
  simpa only [sourceKPArchRadialFlow_mk, sourceKPArchGramCoordinates_mk] using
    sourceKPArchRadialFlowMatrix_coordinates K hζ t g

theorem sourceKPArchRadialFlow_borel (t : ℝ) (b : GL (Fin 2) (InfiniteAdeleRing K))
    (hb : b ∈ sourceKPRingNormalizedBorel (InfiniteAdeleRing K))
    (q : PGL(2, InfiniteAdeleRing K)) :
    sourceKPArchRadialFlow K hζ t (ProjGenLinGroup.mk b*q) =
      ProjGenLinGroup.mk b*sourceKPArchRadialFlow K hζ t q := by
  obtain ⟨g, rfl⟩ := ProjGenLinGroup.mk_surjective q
  rw [← map_mul, sourceKPArchRadialFlow_mk, sourceKPArchRadialFlowMatrix_borel K hζ t b g hb,
    map_mul, sourceKPArchRadialFlow_mk]

theorem sourceKPArchRadialFlow_rationalBorel (t : ℝ) (γ : PGL(2,K))
    (hγ : γ ∈ sourceKPRationalBorel K) (q : PGL(2, InfiniteAdeleRing K)) :
    sourceKPArchRadialFlow K hζ t (sourceKPRationalArchMap K hζ γ*q) =
      sourceKPRationalArchMap K hζ γ*sourceKPArchRadialFlow K hζ t q := by
  obtain ⟨b, hb, rfl⟩ := hγ
  have hb' : GeneralLinearGroup.map (algebraMap K (InfiniteAdeleRing K)) b ∈
      sourceKPRingNormalizedBorel (InfiniteAdeleRing K) := by
    constructor
    · change algebraMap K (InfiniteAdeleRing K) (b 1 0) = 0
      rw [hb.1, map_zero]
    · change algebraMap K (InfiniteAdeleRing K) (b 1 1) = 1
      rw [hb.2, map_one]
  exact sourceKPArchRadialFlow_borel K hζ t _ hb' q

theorem sourceKPArchRadialFlow_compact (t : ℝ) (q k : PGL(2, InfiniteAdeleRing K))
    (hk : k ∈ sourceKPArchBaseCompactSubgroup K hζ) :
    sourceKPArchRadialFlow K hζ t (q*k) = sourceKPArchRadialFlow K hζ t q*k := by
  rw [sourceKPArchRadialFlow, sourceKPArchGramCoordinates_compact K hζ q k hk,
    sourceKPArchRadialFlow, mul_assoc]

theorem sourceKPArchRadialBorelMatrix_continuous :
    Continuous (fun p : ℝ × SourceKPArchUpperHalfSpace K => sourceKPArchRadialBorelMatrix K hζ p.1 p.2) := by
  have hlocal : Continuous (fun p : ℝ × SourceKPArchUpperHalfSpace K =>
      fun v : InfinitePlace K => (sourceKPArchMatrixComplexEquiv K hζ v).symm
        (sourceArchRadialBorel p.1 (p.2 v).1)) := by
    apply continuous_pi
    intro v
    have hv : Continuous (fun p : ℝ × SourceKPArchUpperHalfSpace K => p.2 v) :=
      (_root_.continuous_apply v).comp continuous_snd
    have hz : Continuous (fun p : ℝ × SourceKPArchUpperHalfSpace K => (p.2 v).1) :=
      continuous_fst.comp hv
    have harg : Continuous (fun p : ℝ × SourceKPArchUpperHalfSpace K => (p.1,(p.2 v).1)) :=
      continuous_fst.prodMk hz
    have hh := (sourceKPArchMatrixComplexEquiv_symm_continuous K hζ v).comp
      (sourceArchRadialBorel_continuous.comp harg)
    simpa only [Function.comp_def] using hh
  simpa only [Function.comp_def, sourceKPArchRadialBorelMatrix] using
    (sourceKPArchGLPiEquiv_symm_continuous K).comp hlocal

theorem sourceKPArchRadialFlow_continuous :
    Continuous (fun p : ℝ × PGL(2, InfiniteAdeleRing K) => sourceKPArchRadialFlow K hζ p.1 p.2) := by
  have harg : Continuous (fun p : ℝ × PGL(2, InfiniteAdeleRing K) =>
      (p.1,sourceKPArchGramCoordinates K hζ p.2)) :=
    continuous_fst.prodMk ((sourceKPArchGramCoordinates_continuous K hζ).comp continuous_snd)
  have hh := (sourceKPArchRadialBorelMatrix_continuous K hζ).comp harg
  have hc : Continuous (fun p : ℝ × PGL(2, InfiniteAdeleRing K) =>
      sourceKPArchRadialBorelMatrix K hζ p.1 (sourceKPArchGramCoordinates K hζ p.2)) := by
    simpa only [Function.comp_def] using hh
  change Continuous (fun p : ℝ × PGL(2, InfiniteAdeleRing K) =>
    ProjGenLinGroup.mk (sourceKPArchRadialBorelMatrix K hζ p.1 (sourceKPArchGramCoordinates K hζ p.2)) * p.2)
  have hmk : Continuous (ProjGenLinGroup.mk :
      GL (Fin 2) (InfiniteAdeleRing K) → PGL(2, InfiniteAdeleRing K)) := QuotientGroup.continuous_mk
  exact (hmk.comp hc).mul continuous_snd

theorem sourceKPArchRadialFlowMatrix_height (t : ℝ) (g : GL (Fin 2) (InfiniteAdeleRing K)) :
    sourceKPArchMatrixHeight K hζ (sourceKPArchRadialFlowMatrix K hζ t g) =
      Real.exp (2 * (Fintype.card (InfinitePlace K) : ℝ) * t) * sourceKPArchMatrixHeight K hζ g := by
  have := source_isTotallyComplex K hζ
  unfold sourceKPArchMatrixHeight
  simp_rw [sourceKPArchRadialFlowMatrix_at, sourceArchRadialFlow_height,
    NumberField.IsTotallyComplex.mult_eq, mul_pow]
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_const, Finset.card_univ, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
  congr 1
  ring

def sourceKPFiniteLevelRadialFlow (t : ℝ) (x : SourceKPFiniteLevelSpace K hζ) :
    SourceKPFiniteLevelSpace K hζ := (sourceKPArchRadialFlow K hζ t x.1, x.2)

theorem sourceKPFiniteLevelRadialFlow_finite (t : ℝ) (x : SourceKPFiniteLevelSpace K hζ) :
    (sourceKPFiniteLevelRadialFlow K hζ t x).2 = x.2 := rfl

theorem sourceKPFiniteLevelRadialFlow_zero (x : SourceKPFiniteLevelSpace K hζ) :
    sourceKPFiniteLevelRadialFlow K hζ 0 x = x :=
  Prod.ext (sourceKPArchRadialFlow_zero K hζ x.1) rfl

theorem sourceKPFiniteLevelRadialFlow_add (s t : ℝ) (x : SourceKPFiniteLevelSpace K hζ) :
    sourceKPFiniteLevelRadialFlow K hζ s (sourceKPFiniteLevelRadialFlow K hζ t x) =
      sourceKPFiniteLevelRadialFlow K hζ (s+t) x :=
  Prod.ext (sourceKPArchRadialFlow_add K hζ s t x.1) rfl

theorem sourceKPFiniteLevelRadialFlow_continuous :
    Continuous (fun p : ℝ × SourceKPFiniteLevelSpace K hζ => sourceKPFiniteLevelRadialFlow K hζ p.1 p.2) :=
  ((sourceKPArchRadialFlow_continuous K hζ).comp
    (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).prodMk
      (continuous_snd.comp continuous_snd)

theorem sourceKPFiniteLevelRadialFlow_rationalBorel (t : ℝ) (γ : PGL(2,K))
    (hγ : γ ∈ sourceKPRationalBorel K) (x : SourceKPFiniteLevelSpace K hζ) :
    sourceKPFiniteLevelRadialFlow K hζ t (γ • x) = γ • sourceKPFiniteLevelRadialFlow K hζ t x := by
  apply Prod.ext
  · exact sourceKPArchRadialFlow_rationalBorel K hζ t γ hγ x.1
  · rfl

theorem sourceKPAdelicCoverHeight_archRadial (t : ℝ) (q : SourceKPAdelicProjective K hζ) :
    sourceKPAdelicCoverHeight K hζ (sourceKPArchRadialFlow K hζ t q.1,q.2) =
      Real.exp (2 * (Fintype.card (InfinitePlace K) : ℝ) * t) * sourceKPAdelicCoverHeight K hζ q := by
  obtain ⟨a,b⟩ := q
  obtain ⟨g,rfl⟩ := ProjGenLinGroup.mk_surjective a
  obtain ⟨u,hu⟩ := ProjGenLinGroup.mk_surjective (sourceKPFiniteAdeleProjectiveProjection K hζ b)
  rw [sourceKPArchRadialFlow_mk, sourceKPAdelicCoverHeight_arch_matrix K hζ b u hu.symm,
    sourceKPAdelicCoverHeight_arch_matrix K hζ b u hu.symm,
    sourceKPArchRadialFlowMatrix_height, mul_assoc]

theorem sourceKPFiniteLevelRadialFlow_height (t : ℝ) (x : SourceKPFiniteLevelSpace K hζ) :
    sourceKPFiniteLevelHeight K hζ (sourceKPFiniteLevelRadialFlow K hζ t x) =
      Real.exp (2 * (Fintype.card (InfinitePlace K) : ℝ) * t) * sourceKPFiniteLevelHeight K hζ x := by
  obtain ⟨q,rfl⟩ := sourceKPFiniteLevelMk_surjective K hζ x
  change sourceKPFiniteLevelHeight K hζ
    (sourceKPFiniteLevelMk K hζ (sourceKPArchRadialFlow K hζ t q.1,q.2)) = _
  rw [sourceKPFiniteLevelHeight_mk, sourceKPFiniteLevelHeight_mk,
    sourceKPAdelicCoverHeight_archRadial]

theorem sourceKPFiniteLevelRadialFlow_right_compact (t : ℝ)
    (k : PGL(2, InfiniteAdeleRing K)) (hk : k ∈ sourceKPArchBaseCompactSubgroup K hζ)
    (x : SourceKPFiniteLevelSpace K hζ) :
    sourceKPFiniteLevelRadialFlow K hζ t (x.1*k,x.2) =
      ((sourceKPFiniteLevelRadialFlow K hζ t x).1*k,x.2) :=
  Prod.ext (sourceKPArchRadialFlow_compact K hζ t x.1 k hk) rfl

end
end ArtinMatthews
