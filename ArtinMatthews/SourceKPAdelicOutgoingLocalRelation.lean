module

public import ArtinMatthews.SourceKPAdelicOutgoingLocalReceiver
public import ArtinMatthews.SourceKPAdelicOutgoingRetainedProjection
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

/-! Evaluating the local section over every actual exterior remainder
detects the whole adelic section. In particular, a finite linear
relation between local translates is exactly the corresponding
adelic relation with the actual local lifts. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain
open scoped BigOperators Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K))

local notation "S" => (Singleton.singleton P : Finset (HeightOneSpectrum (𝓞 K)))
local notation "G₀" => SourceFiniteKP2Projective K hζ P
local notation "G" => SourceKPAdelicProjective K hζ
local notation "ι₀" => sourceKPAdelicLocalProjective K hζ P
local notation "Rest" => SourceKPAdelicOutgoingRetainedRest K hζ S
local notation "p₀" => sourceKPAdelicOutgoingSingletonPlace K P
local notation "V" => SourceKPAdelicTorusInducedSpace K hζ
local notation "Vₚ" => SourceKPAdelicPrincipalSeries K hζ
local notation "W" => sourceKPAdelicOutgoingRegularizedRetainedCarrier K hζ S
local notation "R" => sourceKPAdelicOutgoingRegularizedSection K hζ
local notation "R₀" => sourceKPAdelicOutgoingRegularizedLocalSection K hζ P
local notation "ρ" => sourceKPAdelicPrincipalSeriesRepresentation K hζ
local notation "ρ₀" => sourceKPAdelicOutgoingRegularizedLocalBorelRepresentation K hζ P
local notation "π₀" =>
  (fun (s : ℂ) (hs : 0 < Complex.re s) => sourceAlgebraicInducedRepresentation _ (ρ₀ s hs))

theorem sourceKPAdelicOutgoingLocalEval_surjective :
    Function.Surjective (fun q : G₀ × Rest => ι₀ q.1 * q.2.val) := by
  intro g
  obtain ⟨⟨q,r⟩,hq⟩ := sourceKPAdelicOutgoingRetainedEval_surjective K hζ S g
  obtain ⟨a,ha⟩ := sourceKPAdelicOutgoingLocalGroupTuple_surjective K hζ P q
  refine ⟨(a,r), ?_⟩
  change ι₀ a*r.val = g
  rw [← sourceKPAdelicOutgoingLocalGroupTuple_lift K hζ P,ha]
  exact hq

local instance sourceKPAdelicOutgoingLocalRelationTorusAddCommGroup (s : ℂ) :
    AddCommGroup (V s) := Submodule.addCommGroup _

local instance sourceKPAdelicOutgoingLocalRelationPrincipalAddCommGroup (s : ℂ) :
    AddCommGroup (Vₚ s) := Submodule.addCommGroup _

local instance sourceKPAdelicOutgoingLocalRelationCarrierAddCommGroup (s : ℂ) (hs : 0 < s.re) :
    AddCommGroup (W s hs) := Submodule.addCommGroup _

def sourceKPAdelicOutgoingLocalEvaluation (s : ℂ) :
    Vₚ (-s) →ₗ[ℂ] (G₀ → Rest → V (-s)) where
  toFun f q r := f.val (ι₀ q*r.val)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

local notation "A" => sourceKPAdelicOutgoingLocalEvaluation K hζ P

theorem sourceKPAdelicOutgoingLocalEvaluation_injective (s : ℂ) : Function.Injective (A s) := by
  intro f g h
  apply Subtype.ext
  funext u
  obtain ⟨⟨q,r⟩,hu⟩ := sourceKPAdelicOutgoingLocalEval_surjective K hζ P u
  rw [← hu]
  exact congrFun (congrFun h q) r

def sourceKPAdelicOutgoingLocalInducedEvaluation (s : ℂ) (hs : 0 < s.re) :
    sourceAlgebraicInducedSpace _ (ρ₀ s hs) →ₗ[ℂ] (G₀ → Rest → V (-s)) where
  toFun f q r := (f.val q).val r
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

local notation "B" => sourceKPAdelicOutgoingLocalInducedEvaluation K hζ P

theorem sourceKPAdelicOutgoingLocalInducedEvaluation_injective (s : ℂ) (hs : 0 < s.re) :
    Function.Injective (B s hs) := by
  intro f g h
  apply Subtype.ext
  funext q
  apply Subtype.ext
  exact congrFun h q

theorem sourceKPAdelicOutgoingLocalEvaluation_translate (s : ℂ) (hs : 0 < s.re) (a : G₀) :
    B s hs (π₀ s hs a (R₀ s hs).val) = A s (ρ (-s) (ι₀ a) (R s hs)) := by
  funext q r
  change ((R₀ s hs).val.val (q*a)).val r = (R s hs).val ((ι₀ q*r.val)*ι₀ a)
  rw [sourceKPAdelicOutgoingRegularizedLocalSection_apply K hζ P]
  have hc := sourceKPAdelicLocalProjective_commute_of_base_one K hζ P a r.val (r.property p₀)
  rw [map_mul ι₀,mul_assoc,hc.eq,← mul_assoc]

theorem sourceKPAdelicOutgoingLocalTranslate_relation_iff (s : ℂ) (hs : 0 < s.re)
    {ι : Type*} (I : Finset ι) (a : ι → G₀) (c : ι → ℂ) :
    (∑ i ∈ I, c i • π₀ s hs (a i) (R₀ s hs).val) = 0 ↔
      (∑ i ∈ I, c i • ρ (-s) (ι₀ (a i)) (R s hs)) = 0 := by
  have he : B s hs (∑ i ∈ I, c i • π₀ s hs (a i) (R₀ s hs).val) =
      A s (∑ i ∈ I, c i • ρ (-s) (ι₀ (a i)) (R s hs)) := by
    simp only [map_sum,map_smul,sourceKPAdelicOutgoingLocalEvaluation_translate K hζ P s hs]
  have hA : A s 0 = 0 := map_zero (A s)
  have hB : B s hs 0 = 0 := map_zero (B s hs)
  constructor
  · intro h
    apply sourceKPAdelicOutgoingLocalEvaluation_injective K hζ P s
    exact he.symm.trans ((congrArg (⇑(B s hs)) h).trans (hB.trans hA.symm))
  · intro h
    apply sourceKPAdelicOutgoingLocalInducedEvaluation_injective K hζ P s hs
    exact he.trans ((congrArg (⇑(A s)) h).trans (hA.trans hB.symm))

end
end ArtinMatthews
