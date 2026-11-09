module

public import ArtinMatthews.SLocalLogarithm


set_option backward.privateInPublic true
@[expose] public section

/-! Compact boxes in the literal product of S-local multiplicative
groups. The bounds stay away from zero and use genuine local norms. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain SUnitGroup
open scoped NumberField Classical BigOperators
noncomputable section
variable (K : Type) [Field K] [NumberField K]

private theorem isCompact_unitsAnnulus (F : Type*) [NormedField F] [ProperSpace F] (B : ℝ) :
    IsCompact {x : Fˣ | Real.exp (-B) ≤ ‖(x : F)‖ ∧ ‖(x : F)‖ ≤ Real.exp B} := by
  let A : Set F := {x | Real.exp (-B) ≤ ‖x‖ ∧ ‖x‖ ≤ Real.exp B}
  have hAclosed : IsClosed A := isClosed_Icc.preimage continuous_norm
  have hAbounded : Bornology.IsBounded A := by
    rw [isBounded_iff_forall_norm_le]
    exact ⟨Real.exp B, fun x hx => hx.2⟩
  have hAcompact : IsCompact A := Metric.isCompact_iff_isClosed_bounded.mpr ⟨hAclosed, hAbounded⟩
  have hArange : A ⊆ Set.range (Units.val : Fˣ → F) := by
    intro x hx
    have hx0 : x ≠ 0 := by
      intro he
      have hnonpos : Real.exp (-B) ≤ 0 := by simpa only [he, norm_zero] using hx.1
      exact (not_lt_of_ge hnonpos) (Real.exp_pos (-B))
    exact ⟨Units.mk0 x hx0, rfl⟩
  exact (Units.isEmbedding_val₀.isInducing.isCompact_preimage_iff hArange).mpr hAcompact

def sLocalAnnulus (S : Finset (HeightOneSpectrum (𝓞 K))) (B : ℝ) : Set (SWholeUnits K S) :=
  (Set.univ.pi (fun w : InfinitePlace K => InfiniteIdeleGroup.localAnnulus w B)) ×ˢ
    Set.univ.pi (fun v : S => {x : (v.1.adicCompletion K)ˣ |
      Real.exp (-B) ≤ ‖(x : v.1.adicCompletion K)‖ ∧
        ‖(x : v.1.adicCompletion K)‖ ≤ Real.exp B})

theorem sLocalAnnulus_isCompact (S : Finset (HeightOneSpectrum (𝓞 K))) (B : ℝ) :
    IsCompact (sLocalAnnulus K S B) :=
  (isCompact_univ_pi (fun w => InfiniteIdeleGroup.isCompact_localAnnulus w B)).prod
    (isCompact_univ_pi (fun v : S => isCompact_unitsAnnulus (v.1.adicCompletion K) B))

def sLocalNormOneCompact (S : Finset (HeightOneSpectrum (𝓞 K))) (B : ℝ) :
    Set (SWholeUnits K S) :=
  sLocalAnnulus K S B ∩ {y | sLocalLogSum K S (Additive.ofMul y) = 0}

theorem sLocalNormOneCompact_isCompact (S : Finset (HeightOneSpectrum (𝓞 K))) (B : ℝ) :
    IsCompact (sLocalNormOneCompact K S B) :=
  (sLocalAnnulus_isCompact K S B).inter_right
    (isClosed_eq (continuous_sLocalLogSum K S) continuous_const)

theorem sLocalNormOneCompact_norm (S : Finset (HeightOneSpectrum (𝓞 K))) (B : ℝ)
    {y : SWholeUnits K S} (hy : y ∈ sLocalNormOneCompact K S B) : sLocalNorm K S y = 1 :=
  (sLocalNorm_eq_one_iff K S y).mpr hy.2

end
end ArtinMatthews
