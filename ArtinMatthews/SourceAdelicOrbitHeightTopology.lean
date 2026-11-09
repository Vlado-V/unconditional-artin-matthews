module

public import ArtinMatthews.SourceAdelicHeightFibers
public import ArtinMatthews.SourceKPAdelicOrbitHeight
public import Mathlib.Topology.Semicontinuity.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! Continuous finite-level height and lower-semicontinuous rational-orbit
height on the actual automorphic quotient. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Topology
open scoped NumberField MatrixGroups AdeleRing
noncomputable section
variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAdelicCoverHeight_finite_right (q : SourceKPAdelicProjective K hζ)
    (k : sourceKPFiniteDeepMatrixGroup K) :
    sourceKPAdelicCoverHeight K hζ (q * sourceKPFiniteDeepCoverLift K hζ k) =
      sourceKPAdelicCoverHeight K hζ q :=
  sourceKPAdelicCoverHeight_right_deep K hζ q
    ⟨sourceKPFiniteDeepCoverLift K hζ k, ⟨sourceKPFiniteDeepIntoAdelic K hζ k, rfl⟩⟩

theorem sourceKPAdelicOrbitHeight_finite_right (q : SourceKPAdelicProjective K hζ)
    (k : sourceKPFiniteDeepMatrixGroup K) :
    sourceKPAdelicOrbitHeight K hζ (q * sourceKPFiniteDeepCoverLift K hζ k) =
      sourceKPAdelicOrbitHeight K hζ q :=
  sourceKPAdelicOrbitHeight_right_deep K hζ q
    ⟨sourceKPFiniteDeepCoverLift K hζ k, ⟨sourceKPFiniteDeepIntoAdelic K hζ k, rfl⟩⟩

def sourceKPFiniteLevelHeight : SourceKPFiniteLevelSpace K hζ → ℝ :=
  sourceKPFiniteLevelDescend K hζ (sourceKPAdelicCoverHeight K hζ)
    (sourceKPAdelicCoverHeight_finite_right K hζ)

theorem sourceKPFiniteLevelHeight_mk (q : SourceKPAdelicProjective K hζ) :
    sourceKPFiniteLevelHeight K hζ (sourceKPFiniteLevelMk K hζ q) =
      sourceKPAdelicCoverHeight K hζ q := rfl

theorem sourceKPFiniteLevelHeight_pos (x : SourceKPFiniteLevelSpace K hζ) :
    0 < sourceKPFiniteLevelHeight K hζ x := by
  obtain ⟨q, rfl⟩ := sourceKPFiniteLevelMk_surjective K hζ x
  exact sourceKPAdelicCoverHeight_pos K hζ q

theorem sourceKPFiniteLevelHeight_continuous : Continuous (sourceKPFiniteLevelHeight K hζ) :=
  sourceKPFiniteLevelDescend_continuous K hζ _ _ (sourceKPAdelicCoverHeight_arch_continuous K hζ)

theorem sourceKPFiniteLevelHeight_sublevel_closed (T : ℝ) :
    IsClosed {x : SourceKPFiniteLevelSpace K hζ | sourceKPFiniteLevelHeight K hζ x ≤ T} :=
  (sourceKPFiniteLevelHeight_continuous K hζ).lowerSemicontinuous.isClosed_preimage T

def sourceKPFiniteLevelOrbitHeight : SourceKPFiniteLevelSpace K hζ → ℝ :=
  sourceKPFiniteLevelDescend K hζ (sourceKPAdelicOrbitHeight K hζ)
    (sourceKPAdelicOrbitHeight_finite_right K hζ)

theorem sourceKPFiniteLevelOrbitHeight_mk (q : SourceKPAdelicProjective K hζ) :
    sourceKPFiniteLevelOrbitHeight K hζ (sourceKPFiniteLevelMk K hζ q) =
      sourceKPAdelicOrbitHeight K hζ q := rfl

theorem sourceKPFiniteLevelOrbitHeight_pos (x : SourceKPFiniteLevelSpace K hζ) :
    0 < sourceKPFiniteLevelOrbitHeight K hζ x := by
  obtain ⟨q, rfl⟩ := sourceKPFiniteLevelMk_surjective K hζ x
  exact sourceKPAdelicOrbitHeight_pos K hζ q

theorem sourceKPFiniteLevelHeight_le_orbit (x : SourceKPFiniteLevelSpace K hζ) :
    sourceKPFiniteLevelHeight K hζ x ≤ sourceKPFiniteLevelOrbitHeight K hζ x := by
  obtain ⟨q, rfl⟩ := sourceKPFiniteLevelMk_surjective K hζ x
  exact sourceKPAdelicCoverHeight_le_orbit K hζ q

theorem sourceKPFiniteLevelOrbitHeight_eq_iSup (x : SourceKPFiniteLevelSpace K hζ) :
    sourceKPFiniteLevelOrbitHeight K hζ x =
      ⨆ γ : PGL(2,K), sourceKPFiniteLevelHeight K hζ (γ • x) := by
  obtain ⟨q, rfl⟩ := sourceKPFiniteLevelMk_surjective K hζ x
  change sSup (Set.range (fun γ : PGL(2,K) =>
    sourceKPAdelicCoverHeight K hζ (sourceKPAdelicProjectiveRationalLift K hζ γ * q))) =
      sSup (Set.range (fun γ : PGL(2,K) =>
        sourceKPFiniteLevelHeight K hζ (γ • sourceKPFiniteLevelMk K hζ q)))
  apply congrArg sSup
  apply congrArg Set.range
  funext γ
  rw [← sourceKPFiniteLevelMk_rational, sourceKPFiniteLevelHeight_mk]

theorem sourceKPFiniteLevelOrbitHeight_range_bddAbove (x : SourceKPFiniteLevelSpace K hζ) :
    BddAbove (Set.range (fun γ : PGL(2,K) => sourceKPFiniteLevelHeight K hζ (γ • x))) := by
  obtain ⟨q, rfl⟩ := sourceKPFiniteLevelMk_surjective K hζ x
  have he : (fun γ : PGL(2,K) => sourceKPFiniteLevelHeight K hζ (γ • sourceKPFiniteLevelMk K hζ q)) =
      (fun γ : PGL(2,K) => sourceKPAdelicCoverHeight K hζ (sourceKPAdelicProjectiveRationalLift K hζ γ * q)) := by
    funext γ
    rw [← sourceKPFiniteLevelMk_rational, sourceKPFiniteLevelHeight_mk]
  rw [he]
  exact sourceKPAdelicOrbitHeight_range_bddAbove K hζ q

theorem sourceKPFiniteLevelOrbitHeight_lowerSemicontinuous :
    LowerSemicontinuous (sourceKPFiniteLevelOrbitHeight K hζ) := by
  have he : sourceKPFiniteLevelOrbitHeight K hζ =
      (fun x => ⨆ γ : PGL(2,K), sourceKPFiniteLevelHeight K hζ (γ • x)) :=
    funext (sourceKPFiniteLevelOrbitHeight_eq_iSup K hζ)
  rw [he]
  exact lowerSemicontinuous_ciSup (sourceKPFiniteLevelOrbitHeight_range_bddAbove K hζ)
    (fun γ => ((sourceKPFiniteLevelHeight_continuous K hζ).comp
      (sourceKPFiniteLevel_rational_continuous K hζ γ)).lowerSemicontinuous)

theorem sourceKPFiniteLevelOrbitHeight_sublevel_closed (T : ℝ) :
    IsClosed {x : SourceKPFiniteLevelSpace K hζ | sourceKPFiniteLevelOrbitHeight K hζ x ≤ T} :=
  (sourceKPFiniteLevelOrbitHeight_lowerSemicontinuous K hζ).isClosed_preimage T

def sourceKPAutomorphicOrbitHeight : SourceKPAutomorphicLevel K hζ → ℝ :=
  sourceKPAutomorphicLevelDescend K hζ (sourceKPAdelicOrbitHeight K hζ)
    (sourceKPAdelicOrbitHeight_finite_right K hζ)
    (fun γ q => sourceKPAdelicOrbitHeight_rational K hζ q γ)

theorem sourceKPAutomorphicOrbitHeight_mk (q : SourceKPAdelicProjective K hζ) :
    sourceKPAutomorphicOrbitHeight K hζ (sourceKPAutomorphicLevelMk K hζ q) =
      sourceKPAdelicOrbitHeight K hζ q := rfl

theorem sourceKPAutomorphicOrbitHeight_of_finite (x : SourceKPFiniteLevelSpace K hζ) :
    sourceKPAutomorphicOrbitHeight K hζ
      (Quotient.mk (MulAction.orbitRel (PGL(2,K)) (SourceKPFiniteLevelSpace K hζ)) x) =
        sourceKPFiniteLevelOrbitHeight K hζ x := rfl

theorem sourceKPAutomorphicOrbitHeight_pos (x : SourceKPAutomorphicLevel K hζ) :
    0 < sourceKPAutomorphicOrbitHeight K hζ x := by
  obtain ⟨q, rfl⟩ := sourceKPAutomorphicLevelMk_surjective K hζ x
  exact sourceKPAdelicOrbitHeight_pos K hζ q

theorem sourceKPAutomorphicOrbitHeight_lowerSemicontinuous :
    LowerSemicontinuous (sourceKPAutomorphicOrbitHeight K hζ) := by
  apply lowerSemicontinuous_iff_isClosed_preimage.mpr
  intro T
  have hq : IsQuotientMap
      (Quotient.mk (MulAction.orbitRel (PGL(2,K)) (SourceKPFiniteLevelSpace K hζ)) :
        SourceKPFiniteLevelSpace K hζ → SourceKPAutomorphicLevel K hζ) :=
    isQuotientMap_quotient_mk' (s := MulAction.orbitRel (PGL(2,K)) (SourceKPFiniteLevelSpace K hζ))
  apply hq.isClosed_preimage.mp
  change IsClosed {x : SourceKPFiniteLevelSpace K hζ |
    sourceKPAutomorphicOrbitHeight K hζ
      (Quotient.mk (MulAction.orbitRel (PGL(2,K)) (SourceKPFiniteLevelSpace K hζ)) x) ≤ T}
  simpa only [sourceKPAutomorphicOrbitHeight_of_finite] using
    sourceKPFiniteLevelOrbitHeight_sublevel_closed K hζ T

theorem sourceKPAutomorphicOrbitHeight_sublevel_closed (T : ℝ) :
    IsClosed {x : SourceKPAutomorphicLevel K hζ | sourceKPAutomorphicOrbitHeight K hζ x ≤ T} :=
  (sourceKPAutomorphicOrbitHeight_lowerSemicontinuous K hζ).isClosed_preimage T

end
end ArtinMatthews
