module

public import ArtinMatthews.SourceKPReflectedC1Pointwise
public import ArtinMatthews.SourceFrequencyUnitPart
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


set_option backward.privateInPublic true
@[expose] public section

/-! Rational Hilbert reciprocity moves the exterior phase into the
original Weyl phase at the translated retained variable. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix StandardAdelic QuadraticWeil
open scoped NumberField MatrixGroups AdeleRing Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Pr" => HeightOneSpectrum (𝓞 K)
local notation "S" => sourceHilbertSet K S₀
local notation "E" => SourcePrimeExponents K S₀
local notation "σ" => sourceKPTraceJacquetFrequencyAt K
local notation "D" => sourceKPDiagonalHom 𝔸ᶠ[K]
local notation "d" => sourceKPDiagonalHom K
local notation "j" => FiniteAdeleRing.unitEmbedding (𝓞 K) K
local notation "B" => sourceFiniteKPHilbert K hζ
local notation "χ" => sourceKPAdelicCentralComplex K hζ
local notation "ε" => sourceKPCentralComplex K hζ
local notation "tr" => sourceKPRootsTransport K hζ
local notation "ω" => sourceKPReflectedC1WeylPhase K hζ S₀
local notation "κ" => sourceKPReflectedC1ExteriorPhase K hζ S₀

private theorem rational_diagonal_multiplier_one (m a : Kˣ) :
    sourceKPAdeleMultiplier K hζ (D (j m)) (D (j a)) = 1 := by
  have hbase (t : Kˣ) : sourceKPRationalDiagonal K (d t) = D (j t) :=
    sourceKPDiagonalHom_map (algebraMap K 𝔸ᶠ[K]) t
  have hphase (t : Kˣ) : sourceKPRationalPhaseProduct K hζ (d t) = 1 := by
    unfold sourceKPRationalPhaseProduct
    apply finprod_eq_one_of_forall_eq_one
    intro P
    rw [sourceKPRationalLocalPhase, sourceKPAdeleMatrixAt_rational, sourceKPDiagonalHom_map,
      sourceKPDiagonalHom_field, sourceKPFinitePhase_diagonal, map_one]
  have h := sourceKPAdeleMultiplier_rational K hζ (d m) (d a)
  rwa [hbase, hbase, ← map_mul d, hphase, hphase, hphase, one_mul, div_one] at h

theorem sourceKPReflectedC1WeylPhase_eq_product (b : Kˣ) (x : SWholeUnits K S) :
    ω b x = ∏ P : S, (ε P.val (B P.val (σ P.val ((b⁻¹)^2)) (x.2 P) ^ 2) : ℂ) := by
  let C : rootsOfUnity 3 K →* ℂ := (Units.coeHom ℂ).comp χ
  change C (sourceSLocalWeylPhase K S hζ b (sourceKPSLocalReflectionArgument K S b*x⁻¹)) = _
  rw [sourceSLocalWeylPhase_eq_hilbert_product, map_prod]
  apply Finset.prod_congr rfl
  intro P _
  let a := σ P.val ((b⁻¹)^2)
  change (χ ((tr P.val).symm (B P.val a ((a * (x.2 P)⁻¹)⁻¹) ^ 2)) : ℂ) =
    (ε P.val (B P.val a (x.2 P) ^ 2) : ℂ)
  rw [_root_.mul_inv_rev, inv_inv, map_mul (B P.val a), map_inv (B P.val a), sourceFiniteKPHilbert_diag,
    inv_one, mul_one, ← sourceKPAdelicCentralComplex_transport K hζ P.val,
    MulEquiv.apply_symm_apply]

theorem sourceKPReflectedC1ExteriorPhase_mul_retained (e : E) (m b : Kˣ) :
    κ e m b * (∏ P : S, (ε P.val (B P.val (σ P.val m) (σ P.val ((b⁻¹)^2)) ^ 2) : ℂ)) = 1 := by
  let a := (b⁻¹)^2
  let U := sourceKPReflectedC1ExteriorPrimes K S₀ e m b
  let T := sourceKPReflectedExteriorSupport K S (e.support.image Subtype.val) m b
  let f (P : Pr) := (tr P).symm (B P (σ P m) (σ P a) ^ 2)
  let g (P : Pr) : ℂ := (ε P (B P (σ P m) (σ P a) ^ 2) : ℂ)
  have hloc (P : Pr) : sourceKPAdeleLocalMultiplier K hζ (D (j m)) (D (j a)) P = f P := by
    rw [sourceKPAdeleLocalMultiplier_diagonal]
    rfl
  have hrecip := rational_diagonal_multiplier_one K hζ m a
  unfold sourceKPAdeleMultiplier at hrecip
  simp_rw [hloc] at hrecip
  have hout (P : Pr) (hP : P ∉ S ∪ T) : f P = 1 := by
    have hPS : P ∉ S := fun h => hP (Finset.mem_union_left _ h)
    have hn : P ∉ (exteriorPrincipalExponentVector m).support ∪
        (exteriorPrincipalExponentVector b).support ∪ e.support.image Subtype.val :=
      fun h => hP (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨h,hPS⟩))
    have hm : exteriorPrincipalValuation P m = 0 := Finsupp.notMem_support_iff.mp
      (fun h => hn (Finset.mem_union_left _ (Finset.mem_union_left _ h)))
    have hb : exteriorPrincipalValuation P b = 0 := Finsupp.notMem_support_iff.mp
      (fun h => hn (Finset.mem_union_left _ (Finset.mem_union_right _ h)))
    have ha : exteriorPrincipalValuation P a = 0 := by
      rw [show a = (b⁻¹)^2 from rfl, exteriorPrincipalValuation_pow, exteriorPrincipalValuation_inv,
        hb, neg_zero, mul_zero]
    have hv (t : Kˣ) (ht : exteriorPrincipalValuation P t = 0) :
        sourceKPFiniteVal K P (σ P t : P.adicCompletion K) = 1 := by
      change Valued.v (algebraMap K (P.adicCompletion K) (t:K)) = 1
      have hv' : Valued.v (algebraMap K (P.adicCompletion K) (t:K)) = P.valuation K (t:K) :=
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P (t:K)
      rw [hv']
      exact (sourceExteriorPrincipalValuation_eq_zero_iff K P t).mp ht
    unfold f
    rw [sourceFiniteKPHilbert_units K hζ P (source_exterior_six_not_mem K S₀ P hPS)
      _ _ (hv m hm) (hv a ha), one_pow, map_one]
  have hsupp : Function.mulSupport f ⊆ (S ∪ T : Finset Pr) := by
    intro P hP
    by_contra h
    exact hP (hout P h)
  have hdis : Disjoint S T := Finset.disjoint_left.mpr (fun _ hS hT => (Finset.mem_sdiff.mp hT).2 hS)
  rw [finprod_eq_prod_of_mulSupport_subset f hsupp, Finset.prod_union hdis] at hrecip
  let C : rootsOfUnity 3 K →* ℂ := (Units.coeHom ℂ).comp χ
  have hmap (F : Finset Pr) : C (∏ P ∈ F, f P) = ∏ P ∈ F, g P := by
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro P _
    change (χ ((tr P).symm (B P (σ P m) (σ P a) ^ 2)) : ℂ) =
      (ε P (B P (σ P m) (σ P a) ^ 2) : ℂ)
    rw [← sourceKPAdelicCentralComplex_transport K hζ P, MulEquiv.apply_symm_apply]
  have hh := congrArg C hrecip
  rw [map_mul, map_one, hmap, hmap] at hh
  have hT : (∏ P ∈ T, g P) = κ e m b := by
    have hU : U.map (Function.Embedding.subtype (· ∉ S)) = T :=
      sourceKPReflectedC1ExteriorPrimes_map K S₀ e m b
    rw [← hU, Finset.prod_map]
    unfold sourceKPReflectedC1ExteriorPhase
    apply Finset.prod_congr rfl
    intro P _
    have ha : σ P.val a = ((σ P.val b)⁻¹)^2 := by
      unfold a sourceKPTraceJacquetFrequencyAt
      rw [map_pow, map_inv]
    have hp : (Function.Embedding.subtype (fun Q : Pr => Q ∉ S)) P = P.val := rfl
    rw [hp]
    unfold g sourceKPReflectedC1ExteriorPhaseAt
    rw [ha]
  rw [hT, ← Finset.prod_coe_sort] at hh
  exact (mul_comm _ _).trans hh

theorem sourceKPReflectedC1Phase_translate (e : E) (m b : Kˣ) (x : SWholeUnits K S) :
    ω b x * κ e m b = ω b (sWholeDiagonal K S m * x) := by
  let a := (b⁻¹)^2
  let g (P : S) := (ε P.val (B P.val (σ P.val m) (σ P.val a) ^ 2) : ℂ)
  let k (P : S) := (ε P.val (B P.val (σ P.val a) (σ P.val m) ^ 2) : ℂ)
  have hprod : κ e m b * (∏ P : S, g P) = 1 :=
    sourceKPReflectedC1ExteriorPhase_mul_retained K hζ S₀ e m b
  have hpair (P : S) : k P * g P = 1 := by
    have h : B P.val (σ P.val a) (σ P.val m) * B P.val (σ P.val m) (σ P.val a) = 1 := by
      rw [sourceFiniteKPHilbert_skew K hζ P.val (σ P.val a) (σ P.val m), inv_mul_cancel]
    unfold k g
    rw [← Units.val_mul, ← map_mul, ← mul_pow, h, one_pow, map_one]
    rfl
  have hk : (∏ P : S, k P) * (∏ P : S, g P) = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one (fun P _ => hpair P)
  have hg : (∏ P : S, g P) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun _ _ => Units.ne_zero _)
  have he : κ e m b = ∏ P : S, k P := mul_right_cancel₀ hg (hprod.trans hk.symm)
  rw [sourceKPReflectedC1WeylPhase_eq_product, he, sourceKPReflectedC1WeylPhase_eq_product,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro P _
  change _ * k P = (ε P.val (B P.val (σ P.val a) (σ P.val m * x.2 P) ^ 2) : ℂ)
  rw [map_mul (B P.val (σ P.val a)), mul_pow, map_mul, Units.val_mul]
  exact mul_comm _ _

end
end ArtinMatthews
