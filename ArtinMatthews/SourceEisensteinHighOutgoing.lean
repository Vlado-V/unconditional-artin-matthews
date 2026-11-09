module

public import ArtinMatthews.SourceEisensteinOutgoingFiniteLevel
public import ArtinMatthews.SourceEisensteinOutgoingRadial
public import ArtinMatthews.SourceKPTraceIntertwinerRational


set_option backward.privateInPublic true
@[expose] public section

/-! Continuous descent of the genuine outgoing term to the actual high-cusp quotient. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Topology
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPFiniteLevelOutgoingEisenstein_rationalBorel (s : ℂ)
    (b : PGL(2,K)) (hb : b ∈ sourceKPRationalBorel K) (x : SourceKPFiniteLevelSpace K hζ) :
    sourceKPFiniteLevelOutgoingEisenstein K hζ s (b • x) =
      sourceKPFiniteLevelOutgoingEisenstein K hζ s x := by
  obtain ⟨g,rfl⟩ := sourceKPFiniteLevelMk_surjective K hζ x
  rw [← sourceKPFiniteLevelMk_rational, sourceKPFiniteLevelOutgoingEisenstein_mk,
    sourceKPFiniteLevelOutgoingEisenstein_mk, sourceKPAdelicTraceIntertwiner_rationalBorel K hζ s b hb]

def sourceKPHighCuspBorelOutgoingEisenstein (s : ℂ) (T : ℝ) :
    SourceKPHighCuspBorelQuotient K hζ T → ℂ :=
  Quotient.lift (fun x : SourceKPHighCuspFinite K hζ T => sourceKPFiniteLevelOutgoingEisenstein K hζ s x.val)
    (by
      intro x y hxy
      obtain ⟨b,hb⟩ := MulAction.mem_orbit_iff.mp hxy
      rw [← hb]
      exact sourceKPFiniteLevelOutgoingEisenstein_rationalBorel K hζ s b.val b.property y.val)

def sourceKPHighCuspOutgoingEisenstein (s : ℂ) (T : ℝ) (hT : 1 < T) :
    SourceKPHighCuspAutomorphic K hζ T → ℂ :=
  sourceKPHighCuspBorelOutgoingEisenstein K hζ s T ∘ (sourceKPHighCuspHomeomorph K hζ T hT).symm

theorem sourceKPHighCuspOutgoingEisenstein_rep (s : ℂ) (T : ℝ) (hT : 1 < T)
    (x : SourceKPHighCuspFinite K hζ T) :
    sourceKPHighCuspOutgoingEisenstein K hζ s T hT (sourceKPHighCuspProjection K hζ T x) =
      sourceKPFiniteLevelOutgoingEisenstein K hζ s x.val := by
  rw [sourceKPHighCuspOutgoingEisenstein, Function.comp_apply,
    ← sourceKPHighCuspHomeomorph_mk K hζ T hT x, Homeomorph.symm_apply_apply]
  rfl

theorem sourceKPHighCuspOutgoingEisenstein_continuous {s : ℂ} (hs : 0 < s.re)
    (T : ℝ) (hT : 1 < T) : Continuous (sourceKPHighCuspOutgoingEisenstein K hζ s T hT) := by
  have hc : Continuous (sourceKPHighCuspBorelOutgoingEisenstein K hζ s T) :=
    ((sourceKPFiniteLevelOutgoingEisenstein_continuous K hζ hs).comp continuous_subtype_val).quotient_lift _
  exact hc.comp (sourceKPHighCuspHomeomorph K hζ T hT).symm.continuous

theorem sourceKPHighCuspOutgoingEisenstein_include (s : ℂ) {T U : ℝ}
    (hT : 1 < T) (hU : 1 < U) (hTU : T ≤ U) (x : SourceKPHighCuspAutomorphic K hζ U) :
    sourceKPHighCuspOutgoingEisenstein K hζ s T hT ⟨x.val,hTU.trans_lt x.property⟩ =
      sourceKPHighCuspOutgoingEisenstein K hζ s U hU x := by
  obtain ⟨q,rfl⟩ := sourceKPHighCuspQuotientMap_surjective K hζ U x
  induction q using Quotient.inductionOn with
  | _ y =>
    rw [sourceKPHighCuspQuotientMap_mk, sourceKPHighCuspOutgoingEisenstein_rep]
    change sourceKPHighCuspOutgoingEisenstein K hζ s T hT
      (sourceKPHighCuspProjection K hζ T ⟨y.val,hTU.trans_lt y.property⟩) = _
    rw [sourceKPHighCuspOutgoingEisenstein_rep]

theorem sourceKPFiniteLevelOutgoingEisenstein_norm_radial {s : ℂ} (hs : 0 < s.re)
    (t : ℝ) (x : SourceKPFiniteLevelSpace K hζ) :
    ‖sourceKPFiniteLevelOutgoingEisenstein K hζ s (sourceKPFiniteLevelRadialFlow K hζ t x)‖ =
      sourceKPRadialHeightScale K t ^ (1 / 2 - s.re) * ‖sourceKPFiniteLevelOutgoingEisenstein K hζ s x‖ := by
  obtain ⟨g,rfl⟩ := sourceKPFiniteLevelMk_surjective K hζ x
  change ‖sourceKPFiniteLevelOutgoingEisenstein K hζ s
      (sourceKPFiniteLevelMk K hζ (sourceKPArchRadialFlow K hζ t g.1,g.2))‖ = _
  rw [sourceKPFiniteLevelOutgoingEisenstein_mk, sourceKPFiniteLevelOutgoingEisenstein_mk]
  exact sourceKPAdelicTraceIntertwiner_norm_radial K hζ hs t g.1 g.2

theorem sourceKPHighCuspOutgoingEisenstein_norm_radial {s : ℂ} (hs : 0 < s.re)
    (t T : ℝ) (hT : 1 < T) (htT : 1 < sourceKPRadialHeightScale K t*T)
    (x : SourceKPHighCuspAutomorphic K hζ T) :
    ‖sourceKPHighCuspOutgoingEisenstein K hζ s (sourceKPRadialHeightScale K t*T) htT
      (sourceKPHighCuspRadialHomeomorph K hζ t T hT htT x)‖ =
        sourceKPRadialHeightScale K t ^ (1 / 2 - s.re) *
          ‖sourceKPHighCuspOutgoingEisenstein K hζ s T hT x‖ := by
  obtain ⟨q,rfl⟩ := sourceKPHighCuspQuotientMap_surjective K hζ T x
  induction q using Quotient.inductionOn with
  | _ y =>
    rw [sourceKPHighCuspQuotientMap_mk, sourceKPHighCuspRadialHomeomorph_rep,
      sourceKPHighCuspOutgoingEisenstein_rep, sourceKPHighCuspOutgoingEisenstein_rep]
    exact sourceKPFiniteLevelOutgoingEisenstein_norm_radial K hζ hs t y.val

end
end ArtinMatthews
