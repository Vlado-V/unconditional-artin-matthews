module

public import ArtinMatthews.SourceKPReflectedC1PlaceProduct
public import ArtinMatthews.SourceReflectionSignedExteriorProduct
public import ArtinMatthews.SourceKPCuspResidualFourierSymmetries


set_option backward.privateInPublic true
@[expose] public section

/-! The reflected finite coefficient keeps the Weyl center and the
Hilbert multiplier of the two exterior diagonal lifts. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup StandardAdelic QuadraticWeil
open SourceEulerAssembly
open scoped NumberField MatrixGroups AdeleRing Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Pr" => HeightOneSpectrum (𝓞 K)
local notation "S" => sourceHilbertSet K S₀
local notation "P₀" => SourceExteriorPrime K S₀
local notation "E" => SourcePrimeExponents K S₀
local notation "A" => GL (Fin 2) 𝔸ᶠ[K]
local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "M" => sourceKPFiniteAdeleProjectiveMk K hζ
local notation "mk" => sourceFiniteKP2ProjectiveMk K hζ
local notation "Z" => sourceKPFiniteAdeleProjectiveCenter K hζ
local notation "L" => sourceFiniteKP2Lift K hζ
local notation "l" => sourceFiniteKP2ProjectiveLift K hζ
local notation "σ" => sourceKPTraceJacquetFrequencyAt K
local notation "ev" => sourceKPAdeleMatrixAt K
local notation "prod" => sourceKPFiniteCoverPlaceProduct K hζ
local notation "Nf" => sourceKPFiniteAdeleUpperLift K hζ
local notation "tu" => sourceReflectionPositiveTwistAdele K hζ S₀
local notation "C₁" => sourceKPCuspResidualFourierValue K hζ (1 : Kˣ)
local notation "b₀" => fun f d => sourcePrimeExponentUnit K hζ S₀ (sourceReflectionActiveExponents K S₀ f+d)

def sourceKPReflectedC1ExteriorPrimes (e : E) (m b : Kˣ) : Finset P₀ :=
  (sourceKPReflectedExteriorSupport K S (e.support.image Subtype.val) m b).subtype (· ∉ S)

local notation "U" => sourceKPReflectedC1ExteriorPrimes K S₀

theorem sourceKPReflectedC1ExteriorPrimes_map (e : E) (m b : Kˣ) :
    (U e m b).map (Function.Embedding.subtype (· ∉ S)) =
      sourceKPReflectedExteriorSupport K S (e.support.image Subtype.val) m b := by
  apply Finset.subtype_map_of_mem
  intro P hP
  exact (Finset.mem_sdiff.mp hP).2

theorem sourceKPReflectedC1ExteriorPrimes_row_subset (e : E) (m b : Kˣ) :
    e.support ⊆ U e m b := by
  intro P hP
  apply Finset.mem_subtype.mpr
  exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_right _ (Finset.mem_image.mpr ⟨P,hP,rfl⟩),P.property⟩

theorem sourceKPReflectedC1ExteriorPrimes_order_zero (e : E) (m b : Kˣ)
    (P : P₀) (hP : P ∉ U e m b) : exteriorPrincipalValuation P.val (m * (b⁻¹)^2) = 0 := by
  have hT : P.val ∉ (exteriorPrincipalExponentVector m).support ∪
      (exteriorPrincipalExponentVector b).support ∪ e.support.image Subtype.val :=
    fun h => hP (Finset.mem_subtype.mpr (Finset.mem_sdiff.mpr ⟨h,P.property⟩))
  have hm : exteriorPrincipalValuation P.val m = 0 := Finsupp.notMem_support_iff.mp
    (fun h => hT (Finset.mem_union_left _ (Finset.mem_union_left _ h)))
  have hb : exteriorPrincipalValuation P.val b = 0 := Finsupp.notMem_support_iff.mp
    (fun h => hT (Finset.mem_union_left _ (Finset.mem_union_right _ h)))
  rw [exteriorPrincipalValuation_mul, exteriorPrincipalValuation_pow, exteriorPrincipalValuation_inv,
    hm,hb,neg_zero,mul_zero,add_zero]

def sourceKPReflectedC1ExteriorPhaseAt (P : P₀) (m b : Kˣ) : ℂ :=
  (sourceKPCentralComplex K hζ P.val
    (sourceFiniteKPHilbert K hζ P.val (σ P.val m) (((σ P.val b)⁻¹)^2) ^ 2) : ℂ)

def sourceKPReflectedC1ExteriorPhase (e : E) (m b : Kˣ) : ℂ :=
  ∏ P ∈ U e m b, sourceKPReflectedC1ExteriorPhaseAt K hζ S₀ P m b

def sourceKPReflectedC1WeylPhase (b : Kˣ) (x : SWholeUnits K S) : ℂ :=
  (sourceKPAdelicCentralComplex K hζ
    (sourceSLocalWeylPhase K S hζ b (sourceKPSLocalReflectionArgument K S b * x⁻¹)) : ℂ)


theorem sourceKPReflectedC1ExteriorWord_value
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀) (P : P₀) (m b : Kˣ)
    (x : SWholeUnits K S) (u : 𝔸ᶠ[K]) (v : ∀ P : S, P.val.adicCompletion K) (a₀ : A) :
    sourceKPTameCyclicWhittakerValue K hζ S₀ P hS
        (mk P.val (sourceKPReflectedFiniteLocalWord K hζ S m b x u v a₀ P.val)) =
      sourceKPReflectedC1ExteriorPhaseAt K hζ S₀ P m b *
        sourceReflectionSignedExteriorWeylValue K S₀ hζ hS P (m*(b⁻¹)^2) (u P.val) := by
  have hd : σ P.val m * ((σ P.val b)⁻¹)^2 = σ P.val (m*(b⁻¹)^2) := by
    unfold sourceKPTraceJacquetFrequencyAt
    rw [map_mul, map_pow, map_inv]
  have hneg : (-1 : (P.val.adicCompletion K)ˣ) = sourceMinusOneUnit (P.val.adicCompletion K) :=
    Units.ext rfl
  rw [sourceKPReflectedFiniteLocalWord_exterior K hζ S m b x u v a₀ P.val P.property]
  simp only [map_mul]
  change sourceKPTameCyclicWhittakerValue K hζ S₀ P hS
    (l P.val (sourceGL2Diagonal (σ P.val m)) * l P.val (sourceGL2Diagonal (((σ P.val b)⁻¹)^2)) *
      (l P.val (sourceGL2Diagonal (-1)) * l P.val sourceGL2Weyl) * l P.val (sourceGL2Upper (u P.val))) = _
  rw [sourceFiniteKP2ProjectiveLift_diagonal_mul, hd]
  simp only [mul_assoc]
  rw [sourceKPTameCyclicWhittakerValue_center]
  rw [hneg]
  simp only [sourceKPReflectedC1ExteriorPhaseAt, sourceReflectionSignedExteriorWeylValue,
    sourceKPTraceJacquetFrequencyAt, mul_assoc]

theorem sourceKPReflectedC1_pointwise (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)
    {T : ℝ} (hT : 2 < T)
    (m : Kˣ) (f : Finset P₀) (d e : E)
    (h : SourceReflectionPositiveTwistLabels K S₀ e) (x : SWholeUnits K S)
    (R M₀ : S → ℕ) (i : SourceKPRetainedSeedIndex K S R M₀) (a₀ : A) :
    let b := b₀ f d
    let g := Nf (tu e h) * sourceKPRetainedSeedTranslate K hζ S R M₀
      (sourceKPAdelicRootSupportTuple K hζ 1 a₀ S).2 i
    C₁ (one_le_two.trans hT.le) (sourceKPCuspResidualUnitTranslate K hζ m
        (sourceKPReflectedHorizontalFiber K hζ S b g x)) =
      sourceKPReflectedC1WeylPhase K hζ S₀ b x * sourceKPReflectedC1ExteriorPhase K hζ S₀ e m b *
        C₁ (one_le_two.trans hT.le) ((sourceKPLocalCompactProductLift K hζ S
          (sourceKPReflectedC1RetainedWord K hζ S₀ m x R M₀ i a₀)).2) *
        ∏ P ∈ U e m b, sourceReflectionSignedExteriorWeylValue K S₀ hζ hS P
          (m*(b⁻¹)^2) (tu e h P.val) := by
  intro b g
  let v (P : S) : P.val.adicCompletion K := sourceJacquetUpperRepresentative K P.val (R P) (M₀ P) (i P)
  let w := sourceKPReflectedFiniteLocalWord K hζ S m b x (tu e h) v a₀
  let U₀ := U e m b
  let T₀ := sourceKPReflectedExteriorSupport K S (e.support.image Subtype.val) m b
  let j := sourceKPReflectedC1RetainedWord K hζ S₀ m x R M₀ i a₀
  obtain ⟨k,_,hsplit⟩ := sourceKPReflectedFiniteSplit_actual K hζ S₀ m f d e h x R M₀ i a₀
  change sourceKPCuspResidualUnitTranslate K hζ m (sourceKPReflectedHorizontalFiber K hζ S b g x) =
    Z (sourceSLocalWeylPhase K S hζ b (sourceKPSLocalReflectionArgument K S b * x⁻¹)) *
      (M (prod S w) * M (prod T₀ w)) * sourceKPFiniteLevelLift K hζ k at hsplit
  have hbase (P : P₀) (_ : P ∈ U₀) : sourceKPAdelicLocalBase K hζ P.val (1,M (prod S w)) = 1 :=
    sourceKPFiniteCoverPlaceProduct_base_one K hζ S w P.val P.property
  have hfac := sourceKPCuspResidualFourierValue_placeProduct K hζ S₀ hS hT U₀ (M (prod S w)) hbase w
  have hmap : U₀.map (Function.Embedding.subtype (· ∉ S)) = T₀ :=
    sourceKPReflectedC1ExteriorPrimes_map K S₀ e m b
  rw [hmap] at hfac
  have htuple : (fun P : S => mk P.val (w P.val)) = j := by
    funext P
    exact congrArg (mk P.val) (sourceKPReflectedFiniteLocalWord_retained K hζ S m b x (tu e h) v a₀ P
      (sourceReflectionPositiveTwistAdele_zero_retained K hζ S₀ e h P))
  rw [hsplit, sourceKPCuspResidualFourierValue_right_deep, sourceKPCuspResidualFourierValue_center, hfac,
    sourceKPFiniteCoverPlaceProduct_retainedLift K hζ S w, htuple]
  simp only [w, sourceKPReflectedC1ExteriorWord_value K hζ S₀ hS]
  rw [Finset.prod_mul_distrib]
  unfold sourceKPReflectedC1WeylPhase sourceKPReflectedC1ExteriorPhase U₀ j
  ac_rfl

end
end ArtinMatthews
