module

public import ArtinMatthews.SourceKPReflectedFiniteSplit
public import ArtinMatthews.SourceReflectionPositiveFiniteTwist
public import ArtinMatthews.SourceReflectionFrozenWeights


set_option backward.privateInPublic true
@[expose] public section

/-! The signed split uses the original row residue labels, active
denominator and retained seed. The retained set stays fixed. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup SourceEulerAssembly
open scoped NumberField MatrixGroups AdeleRing Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
local notation "S" => sourceHilbertSet K S₀
local notation "Pr" => HeightOneSpectrum (𝓞 K)
local notation "P₀" => SourceExteriorPrime K S₀
local notation "E" => SourcePrimeExponents K S₀
local notation "A" => GL (Fin 2) 𝔸ᶠ[K]
local notation "M" => sourceKPFiniteAdeleProjectiveMk K hζ
local notation "Z" => sourceKPFiniteAdeleProjectiveCenter K hζ
local notation "Nf" => sourceKPFiniteAdeleUpperLift K hζ
local notation "ev" => sourceKPAdeleMatrixAt K
local notation "σ" => sourceKPTraceJacquetFrequencyAt K
local notation "prod" => sourceKPFiniteCoverPlaceProduct K hζ
local notation "u₀" => sourceReflectionPositiveTwistAdele K hζ S₀

theorem sourceReflectionPositiveTwistAdele_at_row (e : E)
    (h : SourceReflectionPositiveTwistLabels K S₀ e) (P : e.support) :
    u₀ e h P.val.val = sourceReflectionPositiveLocalTranslation K hζ S₀ P.val (h P) := by
  let t (Q : e.support) := sourceReflectionPositiveLocalTranslation K hζ S₀ Q.val (h Q)
  change sourceKPAdeleEval K P.val.val (∑ Q : e.support, sourceKPFiniteAdditiveSingle K Q.val.val (t Q)) = t P
  rw [map_sum, Finset.sum_eq_single_of_mem P (Finset.mem_univ P)]
  · exact sourceKPFiniteAdditiveSingle_same K P.val.val (t P)
  · intro Q _ hQ
    exact sourceKPFiniteAdditiveSingle_other K Q.val.val (t Q) P.val.val
      (fun he => hQ (Subtype.ext (Subtype.ext he.symm)))

theorem sourceReflectionPositiveTwistAdele_zero_of_not_mem_row (e : E)
    (h : SourceReflectionPositiveTwistLabels K S₀ e) (P : Pr)
    (hP : P ∉ e.support.image Subtype.val) : u₀ e h P = 0 := by
  let t (Q : e.support) := sourceReflectionPositiveLocalTranslation K hζ S₀ Q.val (h Q)
  change sourceKPAdeleEval K P (∑ Q : e.support, sourceKPFiniteAdditiveSingle K Q.val.val (t Q)) = 0
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro Q _
  exact sourceKPFiniteAdditiveSingle_other K Q.val.val (t Q) P
    (fun he => hP (Finset.mem_image.mpr ⟨Q.val,Q.property,he.symm⟩))

theorem sourceReflectionPositiveTwistAdele_zero_retained (e : E)
    (h : SourceReflectionPositiveTwistLabels K S₀ e) (P : S) : u₀ e h P.val = 0 := by
  apply sourceReflectionPositiveTwistAdele_zero_of_not_mem_row K hζ S₀ e h
  intro hP
  obtain ⟨Q,_,he⟩ := Finset.mem_image.mp hP
  exact Q.property (he.symm ▸ P.property)

theorem sourceKPReflectedFiniteSplit_actual (m : Kˣ) (f : Finset P₀) (d e : E)
    (h : SourceReflectionPositiveTwistLabels K S₀ e) (x : SWholeUnits K S)
    (R M₀ : S → ℕ) (i : SourceKPRetainedSeedIndex K S R M₀) (a₀ : A) :
    let b := sourcePrimeExponentUnit K hζ S₀ (sourceReflectionActiveExponents K S₀ f+d)
    let u := u₀ e h
    let v (P : S) : P.val.adicCompletion K := ↑(sourceJacquetUpperRepresentative K P.val (R P) (M₀ P) (i P))
    let U := sourceKPReflectedExteriorSupport K S (e.support.image Subtype.val) m b
    let g := sourceKPReflectedFiniteLocalWord K hζ S m b x u v a₀
    ∃ k : sourceKPFiniteDeepMatrixGroup K,
      (∀ P : Pr, ev P k.val = if P ∈ S ∪ U then 1 else
        sourceGL2Diagonal (σ P m) * sourceGL2Diagonal (((σ P b)⁻¹)^2) *
          (sourceGL2Diagonal (-1) * sourceGL2Weyl)) ∧
      sourceKPCuspResidualUnitTranslate K hζ m
        (sourceKPReflectedHorizontalFiber K hζ S b
          (Nf u * sourceKPRetainedSeedTranslate K hζ S R M₀ (sourceKPAdelicRootSupportTuple K hζ 1 a₀ S).2 i) x) =
        Z (sourceSLocalWeylPhase K S hζ b (sourceKPSLocalReflectionArgument K S b*x⁻¹)) *
          (M (prod S g) * M (prod U g)) * sourceKPFiniteLevelLift K hζ k := by
  intro b u v U g
  have h6 (P : Pr) (hP : (6 : 𝓞 K) ∈ P.asIdeal) : P ∈ S := by
    by_contra hn
    exact source_exterior_six_not_mem K S₀ P hn hP
  have hv : Nf (sourceKPReflectedRetainedUpper K S v) * (sourceKPAdelicRootSupportTuple K hζ 1 a₀ S).2 =
      sourceKPRetainedSeedTranslate K hζ S R M₀ (sourceKPAdelicRootSupportTuple K hζ 1 a₀ S).2 i := rfl
  rw [← hv]
  exact sourceKPReflectedFiniteSplit K hζ S (e.support.image Subtype.val) h6 m b x u
    (sourceReflectionPositiveTwistAdele_zero_of_not_mem_row K hζ S₀ e h) v a₀

end
end ArtinMatthews
