module

public import ArtinMatthews.SourceKPRetainedSeedSupport
public import ArtinMatthews.SourceKPResidualExteriorProduct
public import ArtinMatthews.SourceKPResidualTameFactor
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

/-! The original exterior factors multiply a seed with trivial exterior
projective components, with the actual commutation in the cubic cover. -/
namespace ArtinMatthews

open NumberField IsDedekindDomain Matrix StandardAdelic QuadraticWeil
open scoped NumberField MatrixGroups AdeleRing Classical BigOperators

noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "Pr" => HeightOneSpectrum (𝓞 K)
local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "A" => GL (Fin 2) 𝔸ᶠ[K]
local notation "B" => sourceKPRetainedFiniteBase K hζ
local notation "D" => sourceKPFiniteAdeleProjectiveDiagonalLift K hζ
local notation "tuple" => sourceKPAdelicRootSupportTuple K hζ
local notation "ev" => sourceKPAdeleMatrixAt K

theorem sourceKPRetainedFiniteBase_tuple_notMem (a : A) (U : Finset Pr)
    (P : Pr) (hP : P ∉ U) : B P (tuple 1 a U).2 = 1 :=
  sourceKPAdelicRootSupportTuple_at_of_not_mem K hζ 1 a U P hP

theorem sourceKPRetainedExteriorTuple_commute (a : A) (U : Finset Pr) (qf : Gf)
    (hq : ∀ P ∈ U, B P qf = 1) : Commute (tuple 1 a U).2 qf := by
  induction U using Finset.induction_on with
  | empty =>
    have he : (tuple 1 a (∅ : Finset Pr)).2 = 1 :=
      (sourceKPFiniteAdeleProjectiveMk K hζ).map_one
    rw [he]
    exact Commute.one_left qf
  | @insert P U hP ih =>
    have hsub (Q : Pr) (hQ : Q ∈ U) : B Q qf = 1 := hq Q (Finset.mem_insert_of_mem hQ)
    let g := sourceFiniteKP2ProjectiveLift K hζ P (ev P a)
    have hcomm := sourceKPAdelicLocalProjective_commute_of_base_one K hζ P g
      ((1,qf) : SourceKPAdelicProjective K hζ) (hq P (Finset.mem_insert_self _ _))
    have hloc : Commute (sourceKPAdelicLocalProjective K hζ P g).2 qf :=
      congrArg Prod.snd hcomm.eq
    rw [congrArg Prod.snd (sourceKPAdelicRootSupportTuple_insert K hζ 1 a U P hP)]
    exact (ih hsub).mul_left hloc

set_option maxRecDepth 4096 in
theorem sourceKPResidualFourierValue_exterior_product_of_supported
    (S₀ : Finset Pr) (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)
    {T : ℝ} (hT : 2 < T) (a : A) (U : Finset Pr) (hUS : Disjoint U (sourceHilbertSet K S₀))
    (qf : Gf) (hq : ∀ P ∈ U, B P qf = 1) :
    sourceKPCuspResidualFourierValue K hζ 1 (one_le_two.trans hT.le) (qf * (tuple 1 a U).2) =
      sourceKPCuspResidualFourierValue K hζ 1 (one_le_two.trans hT.le) qf *
        ∏ P ∈ U, sourceKPResidualExteriorFactor K hζ S₀ hS a P := by
  let W := sourceKPCuspResidualFourierValue K hζ 1 (one_le_two.trans hT.le)
  induction U using Finset.induction_on with
  | empty =>
    have he : (tuple 1 a (∅ : Finset Pr)).2 = 1 :=
      (sourceKPFiniteAdeleProjectiveMk K hζ).map_one
    rw [he, Finset.prod_empty, mul_one, mul_one]
  | @insert P U hP ih =>
    have hPS : P ∉ sourceHilbertSet K S₀ :=
      fun h => (Finset.disjoint_left.mp hUS) (Finset.mem_insert_self _ _) h
    have hUS' : Disjoint U (sourceHilbertSet K S₀) := Finset.disjoint_of_subset_left (Finset.subset_insert _ _) hUS
    have hsub (Q : Pr) (hQ : Q ∈ U) : B Q qf = 1 := hq Q (Finset.mem_insert_of_mem hQ)
    let g := sourceFiniteKP2ProjectiveLift K hζ P (ev P a)
    let q := qf * (tuple 1 a U).2
    have hbase : B P q = 1 := by
      dsimp only [q]
      rw [map_mul, hq P (Finset.mem_insert_self _ _),
        sourceKPRetainedFiniteBase_tuple_notMem K hζ a U P hP, one_mul]
    have htuple : (tuple 1 a (insert P U)).2 =
        (tuple 1 a U).2 * (sourceKPAdelicLocalProjective K hζ P g).2 :=
      congrArg Prod.snd (sourceKPAdelicRootSupportTuple_insert K hζ 1 a U P hP)
    have hfac : sourceKPResidualExteriorFactor K hζ S₀ hS a P =
        sourceKPTameCyclicWhittakerValue K hζ S₀ ⟨P,hPS⟩ hS g := dite_eq_left hPS
    change W (qf*(tuple 1 a (insert P U)).2) = W qf * _
    rw [htuple, ← mul_assoc, Finset.prod_insert hP, hfac]
    change W (q*(sourceKPAdelicLocalProjective K hζ P g).2) = _
    have hbaseFull : sourceKPAdelicLocalBase K hζ P (1,q) = 1 := hbase
    have hW := sourceKPTameResidualFourierValue_factor K hζ S₀ ⟨P,hPS⟩ hS hT q hbaseFull g
    have hI : W q = W qf * ∏ Q ∈ U, sourceKPResidualExteriorFactor K hζ S₀ hS a Q :=
      ih hUS' hsub
    have hW' : W (q*(sourceKPAdelicLocalProjective K hζ P g).2) =
      W q*sourceKPTameCyclicWhittakerValue K hζ S₀ ⟨P,hPS⟩ hS g := hW
    rw [hW', hI]
    ring

end
end ArtinMatthews
