module

public import ArtinMatthews.SourceKPResidualTranslateInjective
public import ArtinMatthews.SourceKPTranslateRepresentativeAE
public import ArtinMatthews.SourceKPCompactChartMassLift


set_option backward.privateInPublic true
@[expose] public section

/-! A relation on the actual common-level Haar space vanishes on every native
archimedean chart at the finite coset of a representative. -/
namespace ArtinMatthews

open NumberField Matrix MeasureTheory Filter SourceHyperbolicGreen
open scoped NumberField MatrixGroups AdeleRing BigOperators

noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
local instance : MeasurableSpace (SourceKPArchSymmetricSpace K hζ) := borel _
local instance : BorelSpace (SourceKPArchSymmetricSpace K hζ) := ⟨rfl⟩

variable (F : Finset (SourceKPFiniteAdeleProjective K hζ))
variable {ι : Type*} [Fintype ι]
variable (t : ι → SourceKPFiniteAdeleProjective K hζ)
variable (ht : ∀ i, sourceKPFiniteTranslateLevel K hζ F ≤ sourceKPFiniteLevelConjugate K hζ (t i))
variable (c : ι → ℂ)

local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "YJ" => SourceKPTranslateAutomorphicCompactLevel K hζ F
local notation "FJ" => SourceKPTranslateFiniteLevelFiber K hζ F
local notation "U" => SourceKPArchUpperHalfSpace K
local notation "A" => PGL(2, InfiniteAdeleRing K)
local notation "μJ" => sourceKPTranslateCompactHaar K hζ F
local notation "μA" => sourceKPArchHaar K hζ
local notation "π[" i "]" => sourceKPTranslateAutomorphicCompactMap K hζ F (t i) (ht i)
local notation "P[" i "]" => sourceKPTranslateGenuinePullbackL2 K hζ F (t i) (ht i)

theorem sourceKPResidualTranslateCombination_coe {T : ℝ} (hT : 2 < T) :
    (sourceKPResidualTranslateCombination K hζ F t ht c hT : YJ → ℂ) =ᵐ[μJ]
      fun y => ∑ i, c i * (sourceKPAutomorphicExceptionalResidue K hζ
        (show 1 ≤ T by linarith)).val (π[i] y) := by
  classical
  let R := sourceKPAutomorphicExceptionalResidue K hζ (show 1 ≤ T by linarith)
  have hi (i : ι) :
      (⇑(c i • P[i] R) : YJ → ℂ) =ᵐ[μJ] fun y => c i * R.val (π[i] y) := by
    filter_upwards [Lp.coeFn_smul (c i) (P[i] R),
      sourceKPTranslateCompactPullbackL2_coe K hζ F (t i) (ht i) R.val] with y h₁ h₂
    exact h₁.trans (congrArg (c i * ·) h₂)
  unfold sourceKPResidualTranslateCombination
  refine (Lp.coeFn_finsetSum Finset.univ (fun i => c i • P[i] R)).trans ?_
  filter_upwards [ae_all_iff.mpr hi] with y hy
  rw [Finset.sum_apply]
  exact Finset.sum_congr rfl (fun i _ => hy i)

theorem sourceKPResidualTranslateCombination_native_zero {T : ℝ} (hT : 2 < T)
    (hz : sourceKPResidualTranslateCombination K hζ F t ht c hT = 0) (qf : Gf) :
    ∀ᵐ p ∂productVolume (InfinitePlace K),
      (∑ i, c i * (sourceKPAutomorphicExceptionalResidue K hζ (show 1 ≤ T by linarith)).val
        (sourceKPCompactCoordinateProjection K hζ (QuotientGroup.mk (qf * t i)) p)) = 0 := by
  classical
  let R := sourceKPAutomorphicExceptionalResidue K hζ (show 1 ≤ T by linarith)
  let qJ := sourceKPTranslateRepresentativeToCompact K hζ F
  let S (p : U) : ℂ :=
    ∑ i, c i * R.val (sourceKPUpperToCompact K hζ (QuotientGroup.mk (qf * t i)) p)
  let e (a : A) : U := sourceKPArchSymmetricHomeomorph K hζ (QuotientGroup.mk a)
  have hS : Measurable S :=
    Finset.measurable_fun_sum _ fun i _ => measurable_const.mul
      ((Lp.stronglyMeasurable R.val).measurable.comp
        (sourceKPUpperToCompact_continuous K hζ (QuotientGroup.mk (qf * t i))).measurable)
  have hY : ∀ᵐ y ∂μJ, (∑ i, c i * R.val (π[i] y)) = 0 := by
    have h := (sourceKPResidualTranslateCombination_coe K hζ F t ht c hT).symm
    rw [hz] at h
    exact h.trans (Lp.coeFn_zero ℂ 2 μJ)
  have hX := (sourceKPTranslateRepresentativeToCompact_full_quasiMeasurePreserving K hζ F).ae hY
  have hprod : ∀ᵐ a ∂μA, ∀ᵐ b ∂(Measure.count : Measure FJ),
      (∑ i, c i * R.val (π[i] (qJ (a,b)))) = 0 :=
    Measure.ae_ae_of_ae_prod hX
  have hA : ∀ᵐ a ∂μA, S (e a) = 0 := by
    filter_upwards [hprod] with a ha
    have ha' := Measure.ae_count_iff.mp ha (QuotientGroup.mk qf)
    simpa only [S, e, qJ, sourceKPTranslateRepresentativeToCompact,
      sourceKPTranslateAutomorphicCompactMap_upperMk, sourceKPFiniteRightTranslateMap_mk] using ha'
  have he : MeasurePreserving e μA (sourceKPArchHyperbolicMeasure K) :=
    (sourceKPArchSymmetricHomeomorph_measurePreserving K hζ).comp (sourceKPArchHaar_projection K hζ)
  have hU : ∀ᵐ p ∂sourceKPArchHyperbolicMeasure K, S p = 0 := by
    rw [← he.map_eq]
    exact (ae_map_iff he.measurable.aemeasurable (measurableSet_eq_fun hS measurable_const)).mpr hA
  exact (sourceKPArchEuclideanUpperMap_preserving K).quasiMeasurePreserving.ae hU

end
end ArtinMatthews
