module

public import ArtinMatthews.SourceKPFiniteCoverSupportedWord
public import ArtinMatthews.SourceKPReflectedFiniteWord
public import ArtinMatthews.SixthExteriorReductionClasses
public import ArtinMatthews.SourceFrequencyUnitPart
public import ArtinMatthews.SourceKPRetainedSeedSupport
public import ArtinMatthews.SourceKubotaGL2Generation
public import ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassPowerLocalUnitQuotient.FinitePlaceCompletionInstances
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! The signed word splits over the fixed retained places and the
actual finite exterior support. Its remaining word is in the fixed level. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open scoped NumberField MatrixGroups AdeleRing Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
local notation "Pr" => HeightOneSpectrum (𝓞 K)
local notation "A" => GL (Fin 2) 𝔸ᶠ[K]
local notation "F" => SourceKPFiniteAdeleCover K hζ
local notation "M" => sourceKPFiniteAdeleProjectiveMk K hζ
local notation "Z" => sourceKPFiniteAdeleProjectiveCenter K hζ
local notation "Nf" => sourceKPFiniteAdeleUpperLift K hζ
local notation "ev" => sourceKPAdeleMatrixAt K
local notation "σ" => sourceKPTraceJacquetFrequencyAt K
local notation "L" => sourceFiniteKP2Lift K hζ
local notation "W" => SourceKPFiniteCoverSupportedWord K hζ
local notation "prod" => sourceKPFiniteCoverPlaceProduct K hζ
local notation "word" => sourceKPReflectedFiniteLocalWord K hζ

def sourceKPReflectedExteriorSupport (S H : Finset Pr) (m b : Kˣ) : Finset Pr :=
  ((exteriorPrincipalExponentVector m).support ∪ (exteriorPrincipalExponentVector b).support ∪ H) \ S

private theorem exteriorSupport_out (S H : Finset Pr) (m b : Kˣ) (P : Pr)
    (hP : P ∉ S ∪ sourceKPReflectedExteriorSupport K S H m b) :
    P ∉ S ∧ P ∉ H ∧ exteriorPrincipalValuation P m = 0 ∧ exteriorPrincipalValuation P b = 0 := by
  have hS : P ∉ S := fun h => hP (Finset.mem_union_left _ h)
  have hT : P ∉ (exteriorPrincipalExponentVector m).support ∪
      (exteriorPrincipalExponentVector b).support ∪ H :=
    fun h => hP (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨h,hS⟩))
  refine ⟨hS, fun h => hT (Finset.mem_union_right _ h), ?_, ?_⟩
  · exact Finsupp.notMem_support_iff.mp (fun h => hT
      (Finset.mem_union_left _ (Finset.mem_union_left _ h)))
  · exact Finsupp.notMem_support_iff.mp (fun h => hT
      (Finset.mem_union_left _ (Finset.mem_union_right _ h)))

private theorem fieldUnitAt_valuation_one (P : Pr) (m : Kˣ) (hm : exteriorPrincipalValuation P m = 0) :
    sourceKPFiniteVal K P (σ P m : P.adicCompletion K) = 1 := by
  change Valued.v ((m : K) : P.adicCompletion K) = 1
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact (sourceExteriorPrincipalValuation_eq_zero_iff K P m).mp hm

private theorem reflectedMatrices_phase (S : Finset Pr) (m b : Kˣ) (x : SWholeUnits K S)
    (u : 𝔸ᶠ[K]) (v : ∀ P : S, P.val.adicCompletion K) (g : A)
    (hg : g ∈ sourceKPReflectedFiniteMatrices K S m b x u v) (P : Pr) :
    sourceKPFinitePhase K hζ P (ev P g) = 1 := by
  simp only [sourceKPReflectedFiniteMatrices, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [sourceKPAdeleMatrixAt_diagonal, sourceKPFinitePhase_diagonal,
      sourceKPAdeleMatrixAt_weyl, sourceKPFinitePhase_weyl,
      sourceKPAdeleMatrixAt_upper, sourceKPFinitePhase_upper]

private theorem reflectedMatrices_integral (S H : Finset Pr) (m b : Kˣ) (x : SWholeUnits K S)
    (u : 𝔸ᶠ[K]) (hu : ∀ P ∉ H, u P = 0) (v : ∀ P : S, P.val.adicCompletion K)
    (g : A) (hg : g ∈ sourceKPReflectedFiniteMatrices K S m b x u v) (P : Pr)
    (hP : P ∉ S ∪ sourceKPReflectedExteriorSupport K S H m b) :
    SourceKPIntegralMatrix (sourceKPFiniteVal K P) (ev P g) := by
  obtain ⟨hS,hH,hm,hb⟩ := exteriorSupport_out K S H m b P hP
  simp only [sourceKPReflectedFiniteMatrices, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [sourceKPAdeleMatrixAt_diagonal]
    change SourceKPIntegralMatrix (sourceKPFiniteVal K P) (sourceGL2Diagonal (σ P m))
    exact sourceKPIntegralMatrix_diagonal _ _ (fieldUnitAt_valuation_one K P m hm)
  · rw [sourceKPReflectedExteriorDiagonal_at K S b P hS]
    apply sourceKPIntegralMatrix_diagonal
    rw [Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, map_pow, map_inv₀,
      fieldUnitAt_valuation_one K P b hb, inv_one, one_pow]
  · rw [sourceKPReflectedRetainedDiagonal_at_exterior K S x P hS]
    exact sourceKPIntegralMatrix_one _
  · rw [sourceKPAdeleMatrixAt_diagonal]
    change SourceKPIntegralMatrix (sourceKPFiniteVal K P) (sourceGL2Diagonal (σ P (-1)))
    apply sourceKPIntegralMatrix_diagonal
    change Valued.v (algebraMap K (P.adicCompletion K) (-1)) = 1
    simp
  · rw [sourceKPAdeleMatrixAt_weyl]
    exact sourceKPIntegralMatrix_weyl _
  · rw [sourceKPAdeleMatrixAt_upper, hu P hH, sourceGL2Upper_zero]
    exact sourceKPIntegralMatrix_one _
  · have hv : sourceKPReflectedRetainedUpper K S v P = 0 := sourceKPRetainedUpperSum_apply_notMem K S v P hS
    rw [sourceKPAdeleMatrixAt_upper, hv, sourceGL2Upper_zero]
    exact sourceKPIntegralMatrix_one _

private theorem supportedWord_list (T : Finset Pr) (h6 : ∀ P ∉ T, (6 : 𝓞 K) ∉ P.asIdeal)
    (l : List A) (hphase : ∀ g ∈ l, ∀ P ∈ T, sourceKPFinitePhase K hζ P (ev P g) = 1)
    (hout : ∀ g ∈ l, ∀ P ∉ T, SourceKPIntegralMatrix (sourceKPFiniteVal K P) (ev P g)) :
    W T (l.map (fun g => (⟨1,g⟩ : F))).prod (fun P => (l.map (fun g => L P (ev P g))).prod) := by
  induction l with
  | nil =>
    simp only [List.map_nil, List.prod_nil]
    refine ⟨fun P => map_one (ev P), ?_, fun P _ => ?_⟩
    · symm
      apply Finset.prod_eq_one
      intro P _
      rw [map_one]
      rfl
    · rw [show (1 : F).base = 1 from rfl, map_one]
      exact sourceKPIntegralMatrix_one _
  | cons g l ih =>
    simp only [List.map_cons, List.prod_cons]
    exact sourceKPFiniteCoverSupportedWord_mul K hζ T h6
      (sourceKPFiniteCoverSupportedWord_canonical K hζ T g
        (hphase g List.mem_cons_self) (hout g List.mem_cons_self))
      (ih (fun a ha => hphase a (List.mem_cons_of_mem g ha))
        (fun a ha => hout a (List.mem_cons_of_mem g ha)))

theorem sourceKPReflectedFiniteCover_supported (S H : Finset Pr)
    (h6 : ∀ P, (6 : 𝓞 K) ∈ P.asIdeal → P ∈ S)
    (m b : Kˣ) (x : SWholeUnits K S) (u : 𝔸ᶠ[K]) (hu : ∀ P ∉ H, u P = 0)
    (v : ∀ P : S, P.val.adicCompletion K) (a₀ : A) :
    let T := S ∪ sourceKPReflectedExteriorSupport K S H m b
    W T (sourceKPReflectedFiniteCover K hζ S m b x u v a₀) (word S m b x u v a₀) := by
  intro T
  have hST : S ⊆ T := Finset.subset_union_left
  have ht (P : Pr) (hP : P ∉ T) (hP6 : (6 : 𝓞 K) ∈ P.asIdeal) : False := hP (hST (h6 P hP6))
  have hL := supportedWord_list K hζ T ht (sourceKPReflectedFiniteMatrices K S m b x u v)
    (fun g hg P _ => reflectedMatrices_phase K hζ S m b x u v g hg P)
    (reflectedMatrices_integral K S H m b x u hu v)
  have hseed := sourceKPFiniteCoverSupportedWord_placeProduct K hζ S T hST (fun P => L P (ev P a₀))
  exact sourceKPFiniteCoverSupportedWord_mul K hζ T ht hL hseed

theorem sourceKPReflectedFiniteSplit (S H : Finset Pr)
    (h6 : ∀ P, (6 : 𝓞 K) ∈ P.asIdeal → P ∈ S)
    (m b : Kˣ) (x : SWholeUnits K S) (u : 𝔸ᶠ[K]) (hu : ∀ P ∉ H, u P = 0)
    (v : ∀ P : S, P.val.adicCompletion K) (a₀ : A) :
    let U := sourceKPReflectedExteriorSupport K S H m b
    let g := word S m b x u v a₀
    ∃ k : sourceKPFiniteDeepMatrixGroup K,
      (∀ P : Pr, ev P k.val = if P ∈ S ∪ U then 1 else
        sourceGL2Diagonal (σ P m) * sourceGL2Diagonal (((σ P b)⁻¹)^2) *
          (sourceGL2Diagonal (-1) * sourceGL2Weyl)) ∧
      sourceKPCuspResidualUnitTranslate K hζ m
        (sourceKPReflectedHorizontalFiber K hζ S b
          (Nf u * (Nf (sourceKPReflectedRetainedUpper K S v) * (sourceKPAdelicRootSupportTuple K hζ 1 a₀ S).2)) x) =
        Z (sourceSLocalWeylPhase K S hζ b (sourceKPSLocalReflectionArgument K S b*x⁻¹)) *
          (M (prod S g) * M (prod U g)) * sourceKPFiniteLevelLift K hζ k := by
  intro U g
  have hs := sourceKPReflectedFiniteCover_supported K hζ S H h6 m b x u hu v a₀
  have hT (P : Pr) (hP : (6 : 𝓞 K) ∈ P.asIdeal) : P ∈ S ∪ U := Finset.mem_union_left _ (h6 P hP)
  obtain ⟨k,hk,he⟩ := sourceKPFiniteCoverSupportedWord_level K hζ (S ∪ U) hT hs
  have hSU : Disjoint S U := Finset.disjoint_sdiff
  refine ⟨k, ?_, ?_⟩
  · intro P
    rw [hk P]
    by_cases hP : P ∈ S ∪ U
    · simp only [ite_eq_left hP]
    · obtain ⟨hPS,hPH,_,_⟩ := exteriorSupport_out K S H m b P hP
      rw [ite_eq_right hP, ite_eq_right hP, hs.coordinate P,
        sourceKPReflectedFiniteLocalWord_exterior K hζ S m b x u v a₀ P hPS,
        hu P hPH, sourceGL2Upper_zero]
      change _ * (1 : GL (Fin 2) (P.adicCompletion K)) = _
      rw [mul_one]
      rfl
  · rw [sourceKPReflectedFiniteCover_mk, he,
      sourceKPFiniteCoverPlaceProduct_union K hζ S U g hSU, map_mul, ← mul_assoc]

end
end ArtinMatthews
