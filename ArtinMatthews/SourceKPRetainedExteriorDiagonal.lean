module

public import ArtinMatthews.SourceKPRetainedDiagonalSplit
public import ArtinMatthews.SourceKPAdelicRootSupportDecomposition
public import ArtinMatthews.SourceKPFiniteIntegralIndex
public import ArtinMatthews.SourceKPIntegralMatrixValuation
public import ArtinMatthews.SourceKPLocalBorelEmbedding
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

/-! A canonical diagonal splits into the literal product of its supported
local diagonal lifts and an actual compact diagonal. The split has phase one. -/
namespace ArtinMatthews

open NumberField IsDedekindDomain Matrix
open scoped NumberField MatrixGroups AdeleRing Classical BigOperators

noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
local notation "Pr" => HeightOneSpectrum (𝓞 K)
local notation "D" => sourceKPFiniteAdeleProjectiveDiagonalLift K hζ
local notation "unitAt" => sourceKPRetainedUnitAt K
local notation "tuple" => sourceKPAdelicRootSupportTuple K hζ
local notation "ev" => sourceKPAdeleMatrixAt K
local notation "diag" => sourceKPDiagonalHom 𝔸ᶠ[K]

private theorem unitPart_eq_prod (U : Finset Pr) (a : 𝔸ᶠ[K]ˣ) :
    sourceKPRetainedUnitPart K U a =
      ∏ P ∈ U, sourceKPAdeleLocalUnit K P (unitAt P a) := by
  unfold sourceKPRetainedUnitPart sourceKPRetainedDiagonalUnit
  simpa only [Finset.univ_eq_attach] using
    (Finset.prod_attach U (fun P => sourceKPAdeleLocalUnit K P (unitAt P a)))

theorem sourceKPRetainedDiagonalLift_unitPart_eq_tuple (U : Finset Pr) (a : 𝔸ᶠ[K]ˣ) :
    D (sourceKPRetainedUnitPart K U a) = (tuple 1 (diag a) U).2 := by
  have hlocal (P : Pr) :
      D (sourceKPAdeleLocalUnit K P (unitAt P a)) =
        (sourceKPAdelicLocalProjective K hζ P
          (sourceFiniteKP2ProjectiveLift K hζ P (ev P (diag a)))).2 := by
    rw [sourceKPAdeleMatrixAt_diagonal]
    exact (congrArg Prod.snd (sourceKPAdelicLocalProjective_diagonal K hζ P (unitAt P a))).symm
  induction U using Finset.induction_on with
  | empty =>
    rw [unitPart_eq_prod, Finset.prod_empty, sourceKPFiniteAdeleProjectiveDiagonalLift_one]
    exact ((sourceKPFiniteAdeleProjectiveMk K hζ).map_one).symm
  | @insert P U hP ih =>
    let l := sourceKPAdeleLocalUnit K P (unitAt P a)
    let r := ∏ Q ∈ U, sourceKPAdeleLocalUnit K Q (unitAt Q a)
    have hdis (Q : Pr) : unitAt Q r = 1 ∨ unitAt Q l = 1 := by
      by_cases hQ : Q = P
      · subst Q
        left
        dsimp only [r]
        rw [map_prod]
        apply Finset.prod_eq_one
        intro Q hQ
        exact sourceKPAdeleLocalUnit_other K Q (unitAt Q a) P (fun h => hP (h ▸ hQ))
      · exact Or.inr (sourceKPAdeleLocalUnit_other K P (unitAt P a) Q hQ)
    have hd : D (l*r) = D r*D l :=
      (congrArg D (mul_comm l r)).trans
        (sourceKPRetainedDiagonalLift_mul_of_disjoint K hζ r l hdis).symm
    have hr : D r = (tuple 1 (diag a) U).2 := by
      simpa only [unitPart_eq_prod] using ih
    rw [unitPart_eq_prod, Finset.prod_insert hP]
    change D (l*r) = _
    rw [hd, hr, hlocal,
      congrArg Prod.snd (sourceKPAdelicRootSupportTuple_insert K hζ 1 (diag a) U P hP)]
    rfl

theorem sourceKPRetainedDiagonalLift_eq_tuple_mul_level (U : Finset Pr) (a : 𝔸ᶠ[K]ˣ)
    (h6 : ∀ P : Pr, (6 : 𝓞 K) ∈ P.asIdeal → ev P (diag a) = 1)
    (hout : ∀ P ∉ U, SourceKPIntegralMatrix (sourceKPFiniteVal K P) (ev P (diag a))) :
    ∃ k : sourceKPFiniteDeepMatrixGroup K,
      D a = (tuple 1 (diag a) U).2 * sourceKPFiniteLevelLift K hζ k := by
  let b := sourceKPRetainedExteriorUnitPart K U a
  have hb (P : Pr) : ev P (diag b) = if P ∈ U then 1 else ev P (diag a) := by
    rw [sourceKPAdeleMatrixAt_diagonal, sourceKPAdeleMatrixAt_diagonal]
    change sourceGL2Diagonal (unitAt P b) = if P ∈ U then 1 else sourceGL2Diagonal (unitAt P a)
    by_cases hP : P ∈ U
    · rw [if_pos hP, sourceKPRetainedExteriorUnitPart_unitAt_mem K U a ⟨P,hP⟩,
        ← sourceKPDiagonalHom_field, map_one]
    · rw [if_neg hP, sourceKPRetainedExteriorUnitPart_unitAt_notMem K U a P hP]
  have hdeep : diag b ∈ sourceKPFiniteDeepMatrixGroup K := by
    apply (sourceKPFiniteDeepMatrixGroup_mem K _).mpr
    constructor
    · intro P
      rw [hb]
      by_cases hP : P ∈ U
      · rw [if_pos hP]
        exact (sourceKPIntegralMatrixMap_mem_range K P 1).mp ⟨1,map_one _⟩
      · rw [if_neg hP]
        exact hout P hP
    · intro P hP
      have he : ev P (diag b) = 1 := by
        rw [hb, h6 P hP]
        split <;> rfl
      rw [he]
      exact (sourceKPDeepLocalBase K P).range.one_mem
  let k : sourceKPFiniteDeepMatrixGroup K := ⟨diag b,hdeep⟩
  have hk : sourceKPFiniteLevelLift K hζ k = D b := by
    rw [sourceKPFiniteLevelLift_eq]
    rfl
  refine ⟨k,?_⟩
  rw [hk, ← sourceKPRetainedDiagonalLift_unitPart_eq_tuple K hζ U a]
  exact sourceKPRetainedDiagonalLift_split K hζ U a

end
end ArtinMatthews
