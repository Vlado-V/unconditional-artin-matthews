module

public import ArtinMatthews.SourceKPLocalTorusCharacter


set_option backward.privateInPublic true
@[expose] public section

/-! Actual good-place unit fixation of the global inducing vector,
and its preservation under Borel actions at other finite places. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain
open scoped NumberField AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K))

theorem sourceKPAdelicLocalUnitIdeles_mem (h6 : (6 : 𝓞 K) ∉ P.asIdeal)
    (u : (P.adicCompletion K)ˣ) (hu : sourceKPFiniteVal K P (u : P.adicCompletion K) = 1) :
    IdeleGroup.ofAdicCompletion (𝓞 K) K P u ∈ sourceKPAdelicUnitIdeles K := by
  refine ⟨?_, ?_, ?_⟩
  · intro Q
    change sourceKPFiniteVal K Q
      ((Units.map (sourceKPAdeleEval K Q).toMonoidHom (sourceKPAdeleLocalUnit K P u)) : Q.adicCompletion K) = 1
    by_cases hQP : Q = P
    · subst Q
      rw [sourceKPAdeleLocalUnit_same]
      exact hu
    · rw [sourceKPAdeleLocalUnit_other K P u Q hQP, Units.val_one, map_one]
  · intro Q hQ
    have hQP : Q ≠ P := by
      intro he
      subst Q
      exact h6 hQ
    refine ⟨1, ?_⟩
    change (1 : (Q.adicCompletion K)ˣ)^3 =
      Units.map (sourceKPAdeleEval K Q).toMonoidHom (sourceKPAdeleLocalUnit K P u)
    rw [one_pow, sourceKPAdeleLocalUnit_other K P u Q hQP]
  · intro w
    change ‖(1 : w.Completion)‖ = 1
    exact norm_one

def sourceKPAdelicLocalUnitTorus (h6 : (6 : 𝓞 K) ∉ P.asIdeal)
    (u : (P.adicCompletion K)ˣ) (hu : sourceKPFiniteVal K P (u : P.adicCompletion K) = 1) :
    sourceKPAdelicUnitTorus K hζ :=
  ⟨sourceKPAdelicLocalTorusSection K hζ P u,
    ⟨⟨IdeleGroup.ofAdicCompletion (𝓞 K) K P u, sourceKPAdelicLocalUnitIdeles_mem K P h6 u hu⟩, rfl⟩⟩

theorem sourceKPAdelicLocalBorelRepresentation_unit_fixed (h6 : (6 : 𝓞 K) ∉ P.asIdeal)
    (s : ℂ) (u : (P.adicCompletion K)ˣ) (hu : sourceKPFiniteVal K P (u : P.adicCompletion K) = 1) :
    sourceKPAdelicLocalBorelRepresentation K hζ P s
      (sourceFiniteKPProjectiveBorelDiagonal K hζ P u) (sourceKPAdelicUnitSphericalVector K hζ s) =
        sourceKPAdelicUnitSphericalVector K hζ s := by
  let x : sourceKPAdelicUnitIdeles K :=
    ⟨IdeleGroup.ofAdicCompletion (𝓞 K) K P u, sourceKPAdelicLocalUnitIdeles_mem K P h6 u hu⟩
  let v := sourceKPAdelicLocalUnitTorus K hζ P h6 u hu
  have hn : sourceKPIdeleAbsoluteNorm K (IdeleGroup.ofAdicCompletion (𝓞 K) K P u) = 1 :=
    sourceKPAdelicUnitIdeles_norm K x
  have hc : (sourceKPIdeleComplexNorm K (1/2 : ℂ)
      (IdeleGroup.ofAdicCompletion (𝓞 K) K P u) : ℂ) = 1 := by
    rw [sourceKPIdeleComplexNorm_coe, hn, Real.log_one, Complex.ofReal_zero,
      mul_zero, Complex.exp_zero]
  rw [sourceKPAdelicLocalBorelRepresentation_diagonal, hc, one_smul]
  exact sourceKPAdelicUnitSphericalVector_right K hζ s v

def sourceKPLocalUnitFixed (s : ℂ) : Submodule ℂ (SourceKPAdelicTorusInducedSpace K hζ s) where
  carrier := {v | ∀ u : (P.adicCompletion K)ˣ,
    sourceKPFiniteVal K P (u : P.adicCompletion K) = 1 →
      sourceKPAdelicLocalBorelRepresentation K hζ P s
        (sourceFiniteKPProjectiveBorelDiagonal K hζ P u) v = v}
  zero_mem' := by intro u hu; exact map_zero _
  add_mem' := by
    intro v w hv hw u hu
    rw [map_add, hv u hu, hw u hu]
  smul_mem' := by
    intro c v hv u hu
    rw [map_smul, hv u hu]

theorem sourceKPLocalUnitFixed_spherical (h6 : (6 : 𝓞 K) ∉ P.asIdeal) (s : ℂ) :
    sourceKPAdelicUnitSphericalVector K hζ s ∈ sourceKPLocalUnitFixed K hζ P s :=
  sourceKPAdelicLocalBorelRepresentation_unit_fixed K hζ P h6 s

theorem sourceKPAdelicLocalBorelRepresentation_commute (s : ℂ)
    (Q : HeightOneSpectrum (𝓞 K)) (hQP : Q ≠ P)
    (b : SourceFiniteKPProjectiveBorel K hζ P) (c : SourceFiniteKPProjectiveBorel K hζ Q) :
    Commute (sourceKPAdelicLocalBorelRepresentation K hζ P s b)
      (sourceKPAdelicLocalBorelRepresentation K hζ Q s c) := by
  have he : sourceKPAdelicLocalBorel K hζ P b * sourceKPAdelicLocalBorel K hζ Q c =
      sourceKPAdelicLocalBorel K hζ Q c * sourceKPAdelicLocalBorel K hζ P b := by
    apply Subtype.ext
    exact (sourceKPAdelicLocalProjective_commute K hζ P Q hQP b.val c.val).eq
  change sourceKPAdelicNormalizedBorelRepresentation K hζ s (sourceKPAdelicLocalBorel K hζ P b) *
      sourceKPAdelicNormalizedBorelRepresentation K hζ s (sourceKPAdelicLocalBorel K hζ Q c) = _
  rw [← map_mul, he, map_mul]
  rfl

theorem sourceKPLocalUnitFixed_other (s : ℂ) (Q : HeightOneSpectrum (𝓞 K)) (hQP : Q ≠ P)
    (c : SourceFiniteKPProjectiveBorel K hζ Q) (v : SourceKPAdelicTorusInducedSpace K hζ s)
    (hv : v ∈ sourceKPLocalUnitFixed K hζ P s) :
    sourceKPAdelicLocalBorelRepresentation K hζ Q s c v ∈ sourceKPLocalUnitFixed K hζ P s := by
  intro u hu
  rw [← Module.End.mul_apply,
    (sourceKPAdelicLocalBorelRepresentation_commute K hζ P s Q hQP
      (sourceFiniteKPProjectiveBorelDiagonal K hζ P u) c).eq,
    Module.End.mul_apply, hv u hu]

end
end ArtinMatthews
