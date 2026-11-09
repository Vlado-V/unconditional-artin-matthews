module

public import ArtinMatthews.SourceKPResidualAdjointTrace
public import ArtinMatthews.SourceKPResidualTraceMean
public import ArtinMatthews.SourceKPResidualCyclicConstantTerm
public import ArtinMatthews.SourceKPResidualTranslateRepresentative
public import ArtinMatthews.SourceKPCompactHighMeanLinear
public import ArtinMatthews.SourceKPAdelicUpperAE


set_option backward.privateInPublic true
@[expose] public section

/-! Vanishing of the trace averages on full representatives gives vanishing
of the adjoint traces in the exceptional nullspace. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory Filter StandardAdelic SourcePhysical
open scoped NumberField AdeleRing MatrixGroups Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (F : Finset (SourceKPFiniteAdeleProjective K hζ))
variable {ι : Type*} [Fintype ι] (t : ι → SourceKPFiniteAdeleProjective K hζ)
variable (ht : ∀ i, sourceKPFiniteTranslateLevel K hζ F ≤ sourceKPFiniteLevelConjugate K hζ (t i))
variable (c : ι → ℂ)
local notation "G" => PGL(2, InfiniteAdeleRing K)
local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "B" => SourceKPFiniteLevelFiber K hζ
local notation "BJ" => SourceKPTranslateFiniteLevelFiber K hζ F
local notation "X" => SourceKPFiniteLevelSpace K hζ
local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "YJ" => SourceKPTranslateAutomorphicCompactLevel K hζ F
local notation "μA" => sourceKPArchHaar K hζ
local notation "μD" => Measure.restrict (sourceKPAdelicTraceProduct K) (sourceKPAdelicFundamentalDomain K)
local notation "ν" => sourceKPFiniteRepresentativeHaar K hζ
local notation "Q" => sourceKPFiniteLevelToCompact K hζ
local notation "N" => sourceKPAdelicUpperLift K hζ
local notation "j" => sourceKPCompactGenuineH1Mass K hζ
local notation "M[" i "]" => sourceKPTranslateAutomorphicCompactMap K hζ F (t i) (ht i)
local notation "Tr[" i "]" => sourceKPTranslateCompactTrace K hζ F (t i) (ht i)
local notation "L[" i "," b "]" => {x : BJ // sourceKPFiniteRightTranslateMap K hζ F (t i) (ht i) x = b}
local instance sourceResidualTranslateKernelAdelicMeasurable : MeasurableSpace 𝔸[K] := borel _

private def residualRepresentative {T : ℝ} (hT : 2 < T) : Y → ℂ :=
  (sourceKPAutomorphicExceptionalResidue K hζ (one_le_two.trans hT.le)).val

variable {T : ℝ} (hT : 2 < T)
local notation "R" => residualRepresentative K hζ hT

private theorem residualTrace_eq_zero_on_representatives
    (hzero : ∀ qf : Gf, ∀ᵐ a ∂μA,
      Integrable (fun z : 𝔸[K] => ∑ i, c i * sourceKPCompactTraceOrbit K hζ R a (qf*t i) z) μD ∧
      (∫ z, ∑ i, c i * sourceKPCompactTraceOrbit K hζ R a (qf*t i) z ∂μD) = 0)
    (i : ι) :
    ∀ᵐ x ∂ν, (∫ z, Tr[i] (fun y : YJ => ∑ k, c k * R (M[k] y)) (Q (N z • x)) ∂μD) = 0 := by
  let v : YJ → ℂ := fun y => ∑ k, c k * R (M[k] y)
  apply (sourceKPFiniteRepresentative_ae_iff_slices K hζ _).mpr
  intro b
  choose qf hqf using fun x : L[i,b] =>
    (QuotientGroup.mk_surjective x.val : ∃ r : Gf, QuotientGroup.mk r = x.val)
  have hsum := ae_all_iff.mpr fun x : L[i,b] => hzero (qf x)
  filter_upwards [hsum] with a ha
  let p (z : 𝔸[K]) := sourceKPArchSymmetricHomeomorph K hζ (QuotientGroup.mk ((N z).1*a))
  let g (z : 𝔸[K]) := (N z).2
  have hQ (z : 𝔸[K]) : Q (N z • ((a,b) : X)) =
      sourceKPUpperToCompact K hζ (g z • b) (p z) :=
    (sourceKPUpperToCompact_mk K hζ (g z • b) ((N z).1*a)).symm
  have he (x : L[i,b]) (z : 𝔸[K]) :
      v (sourceKPTranslateUpperMk K hζ F (p z,g z • x.val)) =
        ∑ k, c k * sourceKPCompactTraceOrbit K hζ R a (qf x*t k) z := by
    have hx : g z • x.val = QuotientGroup.mk (g z*qf x) := by
      rw [← hqf x]
      rfl
    rw [hx]
    change v (sourceKPTranslateAutomorphicCompactMk K hζ F ((N z).1*a) (g z*qf x)) = _
    unfold v
    apply Finset.sum_congr rfl
    intro k _
    rw [sourceKPTranslateAutomorphicCompactMap_mk]
    change c k * R (sourceKPAutomorphicCompactMk K hζ
      (sourceKPAutomorphicLevelMk K hζ ((N z).1*a,((N z).2*qf x)*t k))) =
      c k * R (sourceKPAutomorphicCompactMk K hζ
      (sourceKPAutomorphicLevelMk K hζ ((N z).1*a,(N z).2*(qf x*t k))))
    rw [mul_assoc]
  change (∫ z, Tr[i] v (Q (N z • ((a,b) : X))) ∂μD) = 0
  simp_rw [hQ]
  apply sourceKPTranslateCompactTrace_adelic_integral_eq_zero K hζ F (t i) (ht i) v b p g
  · intro x
    simp_rw [he]
    exact (ha x).1
  · intro x
    simp_rw [he]
    exact (ha x).2

theorem sourceKPResidualTranslateCombination_eq_zero_of_archMean_zero
    (hzero : ∀ qf : Gf, ∀ᵐ a ∂μA,
      Integrable (fun z : 𝔸[K] => ∑ i, c i * sourceKPCompactTraceOrbit K hζ R a (qf*t i) z) μD ∧
      (∫ z, ∑ i, c i * sourceKPCompactTraceOrbit K hζ R a (qf*t i) z ∂μD) = 0) :
    sourceKPResidualTranslateCombination K hζ F t ht c hT = 0 := by
  apply sourceKPResidualTranslateCombination_eq_zero_of_highMean_zero K hζ F t ht c hT
  intro i
  let A := T/2
  let v : YJ → ℂ := fun y => ∑ k, c k * R (M[k] y)
  let W := (j (sourceKPResidualTranslateTestVector K hζ F t ht c hT i)).val
  have htrace : (W : Y → ℂ) =ᵐ[sourceKPAutomorphicCompactMeasure K hζ μA] Tr[i] v :=
    sourceKPResidualTranslateTestVector_trace_ae_of_ae K hζ F t ht c hT i v
      (sourceKPResidualTranslateCombination_coe K hζ F t ht c hT)
  have hA : 1 < A := by dsimp only [A]; linarith
  have hmean := sourceKPCompactHighUnipotentMean_congr_ae K hζ A hA htrace
  have hfull := residualTrace_eq_zero_on_representatives K hζ F t ht c hT hzero i
  have hm := (sourceKPHighRepresentativeHaar_subtype K hζ A).quasiMeasurePreserving
  have hhigh := (hm.ae (hfull.filter_mono ae_restrict_le)).filter_mono
    (ae_restrict_le (s := sourceKPCuspBandHighSection K hζ A))
  filter_upwards [hmean,hhigh] with x hx hz
  rw [hx]
  change (∫ z, Tr[i] v (Q (N z • x.val)) ∂μD) = 0
  exact hz

end
end ArtinMatthews
