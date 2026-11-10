module

public import ArtinMatthews.SourceKPAdeleLocalCover
public import ArtinMatthews.SourceKPFiniteLevel
public import ArtinMatthews.SourceKPFiniteIntegralIndex
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
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
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

/-! Finite products of actual one-place lifts retain their central
coordinates. At the remaining tame places the integral cocycle is one. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open scoped NumberField MatrixGroups AdeleRing Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
local notation "Pr" => HeightOneSpectrum (𝓞 K)
local notation "A" => GL (Fin 2) 𝔸ᶠ[K]
local notation "F" => SourceKPFiniteAdeleCover K hζ
local notation "p" => sourceKPFiniteAdeleProjection K hζ
local notation "ev" => sourceKPAdeleMatrixAt K
local notation "M" => sourceKPFiniteAdeleProjectiveMk K hζ
local notation "emb" => sourceKPAdeleLocalCover K hζ
local notation "μ" => sourceKPAdeleMultiplier K hζ

abbrev SourceKPFiniteCoverLocalWords := (P : Pr) → SourceFiniteKP2Cover K hζ P

local notation "U" => SourceKPFiniteCoverLocalWords K hζ

private theorem phase_one_of_disjoint (a b : A) (h : ∀ P : Pr, ev P a = 1 ∨ ev P b = 1) :
    μ a b = 1 := by
  apply finprod_eq_one_of_forall_eq_one
  intro P
  unfold sourceKPAdeleLocalMultiplier
  rcases h P with hP | hP
  · rw [hP, sourceKPFiniteTwistedMultiplier_one_left, map_one]
  · rw [hP, sourceKPFiniteTwistedMultiplier_one_right, map_one]

def sourceKPFiniteCoverPlaceProduct (T : Finset Pr) (w : U) : F :=
  T.noncommProd (fun P => emb P (w P))
    (fun P _ Q _ hPQ => sourceKPAdeleLocalCover_commute K hζ P Q hPQ.symm _ _)

local notation "prod" => sourceKPFiniteCoverPlaceProduct K hζ

theorem sourceKPFiniteCoverPlaceProduct_insert (T : Finset Pr) (w : U) (P : Pr) (hP : P ∉ T) :
    prod (insert P T) w = emb P (w P) * prod T w :=
  Finset.noncommProd_insert_of_notMem T P _ _ hP

theorem sourceKPFiniteCoverPlaceProduct_union (S T : Finset Pr) (w : U) (h : Disjoint S T) :
    prod (S ∪ T) w = prod S w * prod T w :=
  Finset.noncommProd_union_of_disjoint h _ _

theorem sourceKPFiniteCoverPlaceProduct_at (T : Finset Pr) (w : U) (P : Pr) :
    ev P (prod T w).base = if P ∈ T then (w P).base else 1 := by
  induction T using Finset.induction_on with
  | empty =>
    change ev P (p 1) = _
    simp only [map_one, Finset.notMem_empty, if_false]
  | @insert Q T hQ ih =>
    rw [sourceKPFiniteCoverPlaceProduct_insert K hζ T w Q hQ]
    change ev P (p (emb Q (w Q) * prod T w)) = _
    rw [map_mul p, map_mul (ev P)]
    change ev P (sourceKPAdeleSingleMatrix K Q (w Q).base) * ev P (prod T w).base = _
    rw [ih]
    by_cases he : P = Q
    · subst Q
      rw [sourceKPAdeleSingleMatrix_same, if_neg hQ, mul_one, if_pos (Finset.mem_insert_self _ _)]
    · rw [sourceKPAdeleSingleMatrix_other K Q P he, one_mul]
      simp only [Finset.mem_insert, he, false_or]

theorem sourceKPFiniteCoverPlaceProduct_central (T : Finset Pr) (w : U) :
    (prod T w).central = ∏ P ∈ T, (emb P (w P)).central := by
  induction T using Finset.induction_on with
  | empty => rfl
  | @insert P T hP ih =>
    rw [sourceKPFiniteCoverPlaceProduct_insert K hζ T w P hP, Finset.prod_insert hP]
    have hμ : μ (emb P (w P)).base (prod T w).base = 1 := by
      apply phase_one_of_disjoint K hζ
      intro Q
      by_cases he : Q = P
      · subst Q
        exact Or.inr (by rw [sourceKPFiniteCoverPlaceProduct_at K hζ T w P, if_neg hP])
      · exact Or.inl (sourceKPAdeleSingleMatrix_other K P Q he (w P).base)
    change (emb P (w P)).central * (prod T w).central *
      μ (emb P (w P)).base (prod T w).base = _
    rw [hμ, mul_one, ih]

structure SourceKPFiniteCoverSupportedWord (T : Finset Pr) (a : F) (w : U) : Prop where
  coordinate : ∀ P, ev P a.base = (w P).base
  central : a.central = ∏ P ∈ T, (emb P (w P)).central
  integral : ∀ P ∉ T, SourceKPIntegralMatrix (sourceKPFiniteVal K P) (ev P a.base)

local notation "W" => SourceKPFiniteCoverSupportedWord K hζ

theorem sourceKPFiniteCoverSupportedWord_canonical (T : Finset Pr) (a : A)
    (hphase : ∀ P ∈ T, sourceKPFinitePhase K hζ P (ev P a) = 1)
    (hout : ∀ P ∉ T, SourceKPIntegralMatrix (sourceKPFiniteVal K P) (ev P a)) :
    W T ⟨1,a⟩ (fun P => sourceFiniteKP2Lift K hζ P (ev P a)) := by
  refine ⟨fun _ => rfl, ?_, hout⟩
  symm
  apply Finset.prod_eq_one
  intro P hP
  change (sourceKPRootsTransport K hζ P).symm (1 / sourceKPFinitePhase K hζ P (ev P a)) = 1
  rw [hphase P hP, div_one, map_one]

theorem sourceKPFiniteCoverSupportedWord_placeProduct (S T : Finset Pr) (hST : S ⊆ T) (w : U) :
    W T (prod S w) (fun P => if P ∈ S then w P else 1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro P
    rw [sourceKPFiniteCoverPlaceProduct_at K hζ S w P]
    split_ifs <;> rfl
  · rw [sourceKPFiniteCoverPlaceProduct_central K hζ S w]
    calc
      _ = ∏ P ∈ S, (emb P (if P ∈ S then w P else 1)).central := by
        apply Finset.prod_congr rfl
        intro P hP
        rw [if_pos hP]
      _ = _ := by
        apply Finset.prod_subset hST
        intro P _ hP
        rw [if_neg hP, map_one]
        rfl
  · intro P hP
    rw [sourceKPFiniteCoverPlaceProduct_at K hζ S w P, if_neg (fun h => hP (hST h))]
    exact sourceKPIntegralMatrix_one _

theorem sourceKPFiniteCoverSupportedWord_mul (T : Finset Pr)
    (h6 : ∀ P ∉ T, (6 : 𝓞 K) ∉ P.asIdeal) {a b : F} {w v : U}
    (ha : W T a w) (hb : W T b v) : W T (a*b) (fun P => w P*v P) := by
  have hμ : μ a.base b.base = ∏ P ∈ T, sourceKPAdeleLocalMultiplier K hζ a.base b.base P := by
    unfold sourceKPAdeleMultiplier
    apply finprod_eq_prod_of_mulSupport_subset
    intro P hP
    by_contra hn
    apply hP
    unfold sourceKPAdeleLocalMultiplier
    rw [sourceKPFiniteTwistedMultiplier_of_integral K hζ P (h6 P hn) _ _
      (ha.integral P hn) (hb.integral P hn), map_one]
  have he (P : Pr) : (emb P (w P*v P)).central =
      (emb P (w P)).central * (emb P (v P)).central *
        sourceKPAdeleLocalMultiplier K hζ a.base b.base P := by
    rw [map_mul]
    change _ * _ * μ (sourceKPAdeleSingleMatrix K P (w P).base)
      (sourceKPAdeleSingleMatrix K P (v P).base) = _
    rw [sourceKPAdeleMultiplier_single K hζ P, ← ha.coordinate P, ← hb.coordinate P]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · intro P
    change ev P (a.base*b.base) = (w P).base*(v P).base
    rw [map_mul, ha.coordinate P, hb.coordinate P]
  · change a.central*b.central*μ a.base b.base = _
    rw [ha.central, hb.central, hμ]
    simp only [he, Finset.prod_mul_distrib]
  · intro P hP
    change SourceKPIntegralMatrix (sourceKPFiniteVal K P) (ev P (a.base*b.base))
    rw [map_mul]
    exact sourceKPIntegralMatrix_mul _ (ha.integral P hP) (hb.integral P hP)

theorem sourceKPFiniteCoverSupportedWord_level (T : Finset Pr)
    (h6 : ∀ P, (6 : 𝓞 K) ∈ P.asIdeal → P ∈ T) {a : F} {w : U} (ha : W T a w) :
    ∃ k : sourceKPFiniteDeepMatrixGroup K,
      (∀ P, ev P k.val = if P ∈ T then 1 else ev P a.base) ∧
      M a = M (prod T w) * sourceKPFiniteLevelLift K hζ k := by
  let l := prod T w
  let r := l.base⁻¹*a.base
  have hr (P : Pr) : ev P r = if P ∈ T then 1 else ev P a.base := by
    change ev P (l.base⁻¹*a.base) = _
    rw [map_mul, map_inv, show l = prod T w from rfl, sourceKPFiniteCoverPlaceProduct_at K hζ T w P]
    by_cases hP : P ∈ T
    · rw [if_pos hP, if_pos hP, ha.coordinate P, inv_mul_cancel]
    · rw [if_neg hP, if_neg hP, inv_one, one_mul]
  have hk : r ∈ sourceKPFiniteDeepMatrixGroup K := by
    apply (sourceKPFiniteDeepMatrixGroup_mem K r).mpr
    constructor
    · intro P
      by_cases hP : P ∈ T
      · rw [hr P, if_pos hP]
        exact sourceKPIntegralMatrix_one _
      · rw [hr P, if_neg hP]
        exact ha.integral P hP
    · intro P hP
      rw [hr P, if_pos (h6 P hP)]
      exact (sourceKPDeepLocalBase K P).range.one_mem
  let k : sourceKPFiniteDeepMatrixGroup K := ⟨r,hk⟩
  have hμ : μ l.base r = 1 := by
    apply phase_one_of_disjoint K hζ
    intro P
    by_cases hP : P ∈ T
    · exact Or.inr (by rw [hr P, if_pos hP])
    · exact Or.inl (by rw [show l = prod T w from rfl, sourceKPFiniteCoverPlaceProduct_at K hζ T w P, if_neg hP])
  have he : a = l * (⟨1,r⟩ : F) := by
    apply SourceKPFiniteAdeleCover.ext K hζ
    · change a.central = l.central*1*μ l.base r
      rw [hμ, mul_one, mul_one, show l = prod T w from rfl, sourceKPFiniteCoverPlaceProduct_central, ha.central]
    · change a.base = l.base*(l.base⁻¹*a.base)
      rw [mul_inv_cancel_left]
  refine ⟨k, hr, ?_⟩
  have hl : sourceKPFiniteLevelLift K hζ k = M ⟨1,r⟩ := by
    rw [sourceKPFiniteLevelLift_eq]
    rfl
  rw [hl, ← map_mul, ← he]

end
end ArtinMatthews
