module

public import ArtinMatthews.SourceKPRetainedExteriorWhittaker
public import ArtinMatthews.SourceKPResidualExteriorProduct
public import ArtinMatthews.SourceKPRetainedDiagonalSplit
public import ArtinMatthews.SourceKPIntegralMatrixValuation
public import ArtinMatthews.SourceKPRetainedExteriorDiagonal
public import ArtinMatthews.SourceKPRetainedExteriorLocalSupport
public import ArtinMatthews.SourceKPRetainedPrincipalTransport
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

/-! At arbitrary rational frequencies the actual exterior diagonal
splits over precisely the nonzero exterior orders, followed by the deep
compact lift. Sixth powers have trivial diagonal phase. -/
namespace ArtinMatthews

open NumberField IsDedekindDomain Matrix AllowedGenerators VaryingKummerAnalytic
open StandardAdelic QuadraticWeil
open scoped NumberField MatrixGroups AdeleRing Classical BigOperators

noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "Pr" => HeightOneSpectrum (𝓞 K)
local notation "D" => sourceKPFiniteAdeleProjectiveDiagonalLift K hζ
local notation "unitAt" => sourceKPRetainedUnitAt K
local notation "loc" => sourceKPRetainedRationalLocalUnit K
local notation "tuple" => sourceKPAdelicRootSupportTuple K hζ
local notation "ev" => sourceKPAdeleMatrixAt K
local notation "rUnit" => FiniteAdeleRing.unitEmbedding (𝓞 K) K
local notation "diag" => sourceKPDiagonalHom 𝔸ᶠ[K]
local notation "S[" S₀ "]" => sourceHilbertSet K S₀

theorem sourceKPRetainedPrincipalExterior_all
    (S₀ : Finset Pr) (hS : standardWeilBadPlaces K ⊆ S[S₀]) (m : Kˣ) :
    let b := sourceKPRetainedExteriorUnitPart K S[S₀] (rUnit m)
    let A₀ := diag b
    let U := (sourceKPRetainedExteriorOrderSupport K S₀ m).image Subtype.val
    ∃ k : sourceKPFiniteDeepMatrixGroup K,
      Disjoint U S[S₀] ∧
      D b = (tuple 1 A₀ U).2 * sourceKPFiniteLevelLift K hζ k ∧
      (∏ P ∈ U, sourceKPResidualExteriorFactor K hζ S₀ hS A₀ P) =
        sourceKPRetainedExteriorWhittaker K hζ S₀ hS m := by
  let S := S[S₀]
  let b := sourceKPRetainedExteriorUnitPart K S (rUnit m)
  let A₀ := diag b
  let T := sourceKPRetainedExteriorOrderSupport K S₀ m
  let U : Finset Pr := T.image Subtype.val
  have hUS : Disjoint U S := by
    apply Finset.disjoint_left.mpr
    intro P hP hPS
    obtain ⟨Q,_,rfl⟩ := Finset.mem_image.mp hP
    exact Q.property hPS
  have hext (P : Pr) (hP : P ∉ S) : ev P A₀ = sourceGL2Diagonal (loc P m) := by
    change ev P (diag b) = _
    rw [sourceKPAdeleMatrixAt_diagonal]
    change sourceGL2Diagonal (unitAt P b) = _
    rw [sourceKPRetainedExteriorUnitPart_unitAt_notMem K S (rUnit m) P hP,
      sourceKPRetainedUnitAt_rational]
    rfl
  have hret (P : Pr) (hP : P ∈ S) : ev P A₀ = 1 := by
    change ev P (diag b) = _
    rw [sourceKPAdeleMatrixAt_diagonal]
    change sourceGL2Diagonal (unitAt P b) = _
    rw [sourceKPRetainedExteriorUnitPart_unitAt_mem K S (rUnit m) ⟨P,hP⟩,
      ← sourceKPDiagonalHom_field, map_one]
  have h6 (P : Pr) (hP : (6 : 𝓞 K) ∈ P.asIdeal) : ev P A₀ = 1 := by
    apply hret
    by_contra hn
    exact source_exterior_six_not_mem K S₀ P hn hP
  have hout (P : Pr) (hP : P ∉ U) : SourceKPIntegralMatrix (sourceKPFiniteVal K P) (ev P A₀) := by
    by_cases hPS : P ∈ S
    · rw [hret P hPS]
      exact (sourceKPIntegralMatrixMap_mem_range K P 1).mp ⟨1,map_one _⟩
    have hzero : exteriorPrincipalValuation P m = 0 := by
      by_contra hn
      have ht := (sourceKPRetainedExteriorOrderSupport_mem K S₀ m ⟨P,hPS⟩).mpr hn
      exact hP (Finset.mem_image.mpr ⟨⟨P,hPS⟩,ht,rfl⟩)
    rw [hext P hPS]
    apply sourceKPIntegralMatrix_diagonal
    rw [sourceKPRetainedRationalLocalUnit_valuation, hzero, neg_zero, WithZero.exp_zero]
  obtain ⟨k,hk⟩ := sourceKPRetainedDiagonalLift_eq_tuple_mul_level K hζ U b h6 hout
  refine ⟨k,hUS,hk,?_⟩
  change (∏ P ∈ T.image Subtype.val, sourceKPResidualExteriorFactor K hζ S₀ hS A₀ P) = _
  rw [sourceKPRetainedExteriorWhittaker_eq_prod K hζ S₀ hS m,
    Finset.prod_image (fun P _ Q _ h => Subtype.ext h)]
  apply Finset.prod_congr rfl
  intro P _
  rw [sourceKPResidualExteriorFactor, dite_eq_left P.property, hext P.val P.property]
  rfl

theorem sourceKPRetainedExteriorDiagonalPhase_sixth
    (S : Finset Pr) (m r : Kˣ) :
    sourceKPRetainedDiagonalPhase K hζ
      (sourceKPRetainedExteriorUnitPart K S (rUnit m))
      (sourceKPRetainedExteriorUnitPart K S (rUnit r)^6) = 1 := by
  rw [show (6:ℕ) = 2*3 from rfl, pow_mul]
  exact sourceKPAdeleMultiplier_diagonal_cube_right K hζ _ _

theorem sourceKPRetainedExteriorRationalDiagonal_mul_sixth (S : Finset Pr) (m r : Kˣ) :
    D (sourceKPRetainedExteriorUnitPart K S (rUnit (m*r^6))) =
      D (sourceKPRetainedExteriorUnitPart K S (rUnit m)) *
        D (sourceKPRetainedExteriorUnitPart K S (rUnit r)^6) := by
  let u := sourceKPRetainedExteriorUnitPart K S (rUnit m)
  let v := sourceKPRetainedExteriorUnitPart K S (rUnit r)
  have he : sourceKPRetainedExteriorUnitPart K S (rUnit (m*r^6)) = u*v^6 := by
    apply Units.ext
    apply FiniteAdeleRing.ext
    intro P
    have h : unitAt P (sourceKPRetainedExteriorUnitPart K S (rUnit (m*r^6))) =
        unitAt P (u*v^6) := by
      rw [(unitAt P).map_mul u (v^6), (unitAt P).map_pow v 6]
      by_cases hP : P ∈ S
      · rw [sourceKPRetainedExteriorUnitPart_unitAt_mem K S _ ⟨P,hP⟩,
          show unitAt P u = 1 from sourceKPRetainedExteriorUnitPart_unitAt_mem K S _ ⟨P,hP⟩,
          show unitAt P v = 1 from sourceKPRetainedExteriorUnitPart_unitAt_mem K S _ ⟨P,hP⟩,
          one_pow,one_mul]
      · rw [sourceKPRetainedExteriorUnitPart_unitAt_notMem K S _ P hP,
          show unitAt P u = unitAt P (rUnit m) from
            sourceKPRetainedExteriorUnitPart_unitAt_notMem K S _ P hP,
          show unitAt P v = unitAt P (rUnit r) from
            sourceKPRetainedExteriorUnitPart_unitAt_notMem K S _ P hP]
        simp only [map_mul,map_pow]
    exact congrArg Units.val h
  change D (sourceKPRetainedExteriorUnitPart K S (rUnit (m*r^6))) = D u*D (v^6)
  rw [he,sourceKPRetainedDiagonalLift_mul_phase]
  have hp : sourceKPRetainedDiagonalPhase K hζ u (v^6) = 1 :=
    sourceKPRetainedExteriorDiagonalPhase_sixth K hζ S m r
  rw [hp,map_one,one_mul]

end
end ArtinMatthews
