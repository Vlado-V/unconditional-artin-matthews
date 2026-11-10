module

public import ClassFieldTheory.AlgebraicNumberTheory.RayClass.FullModulus
public import Mathlib.NumberTheory.NumberField.FiniteAdeleRing
public import ArtinMatthews.SourceKPCFTIdeleBridge
public import ClassFieldTheory.AlgebraicNumberTheory.RayClass.Topology
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Fixed finite ray labels and exact finite-idelic representatives.
The principal correction is retained as an actual element of the field. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain
open scoped NumberField AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K]

def sourceKPFiniteRaySubgroup (n : RayClass.FiniteModulus K) : Subgroup (_root_.IdeleGroup K) :=
  (RayClass.Modulus.ofFinite n).ideleCongruenceSubgroup ⊔ _root_.IdeleGroup.principalSubgroup K

abbrev SourceKPFiniteRayLabels (n : RayClass.FiniteModulus K) :=
  _root_.IdeleGroup K ⧸ sourceKPFiniteRaySubgroup K n

instance sourceKPFiniteRayLabels_fintype (n : RayClass.FiniteModulus K) :
    Fintype (SourceKPFiniteRayLabels K n) := by
  letI : (sourceKPFiniteRaySubgroup K n).FiniteIndex :=
    RayClass.ideleCongruenceSupPrincipalFiniteIndex (RayClass.Modulus.ofFinite n)
  exact Fintype.ofFinite _

def sourceKPFiniteRayLabel (n : RayClass.FiniteModulus K) (a : _root_.FiniteIdeleGroup K) :
    SourceKPFiniteRayLabels K n :=
  QuotientGroup.mk ((1,a) : _root_.IdeleGroup K)

def sourceKPFiniteRayRepresentative (n : RayClass.FiniteModulus K)
    (i : SourceKPFiniteRayLabels K n) : _root_.FiniteIdeleGroup K :=
  (Quotient.out i : _root_.IdeleGroup K).2

theorem sourceKPFiniteRay_decomposition (n : RayClass.FiniteModulus K)
    (a : _root_.FiniteIdeleGroup K) :
    ∃ q : Kˣ, ∃ u : RayClass.finiteCongruenceSubgroup n,
      a = (_root_.IdeleGroup.principalIdele K q).2 *
        sourceKPFiniteRayRepresentative K n (sourceKPFiniteRayLabel K n a) * u.val := by
  let r : _root_.IdeleGroup K := Quotient.out (sourceKPFiniteRayLabel K n a)
  have hc : (QuotientGroup.mk r : SourceKPFiniteRayLabels K n) =
      QuotientGroup.mk ((1,a) : _root_.IdeleGroup K) :=
    Quotient.out_eq (sourceKPFiniteRayLabel K n a)
  have hm := QuotientGroup.eq.mp hc
  change r⁻¹ * ((1,a) : _root_.IdeleGroup K) ∈
    (RayClass.Modulus.ofFinite n).ideleCongruenceSubgroup ⊔ _root_.IdeleGroup.principalSubgroup K at hm
  obtain ⟨b,hb,p,hp,hbp⟩ := Subgroup.mem_sup_of_normal_right.mp hm
  obtain ⟨q,rfl⟩ := hp
  have hu : b.2 ∈ RayClass.finiteCongruenceSubgroup n := hb.2
  refine ⟨q,⟨b.2,hu⟩,?_⟩
  have he : r * (b * _root_.IdeleGroup.principalIdele K q) = ((1,a) : _root_.IdeleGroup K) := by
    rw [hbp]
    group
  have hf := congrArg Prod.snd he
  change r.2 * (b.2 * (_root_.IdeleGroup.principalIdele K q).2) = a at hf
  change a = (_root_.IdeleGroup.principalIdele K q).2 * r.2 * b.2
  rw [← hf]
  ac_rfl

def sourceKPFiniteRayAdeleLabel (n : RayClass.FiniteModulus K) (a : (𝔸ᶠ[K])ˣ) :
    SourceKPFiniteRayLabels K n :=
  sourceKPFiniteRayLabel K n ((_root_.IdeleGroup.finiteEquivFiniteAdeleUnits (K := K)).symm a)

def sourceKPFiniteRayAdeleRepresentative (n : RayClass.FiniteModulus K)
    (i : SourceKPFiniteRayLabels K n) : (𝔸ᶠ[K])ˣ :=
  _root_.IdeleGroup.finiteEquivFiniteAdeleUnits (sourceKPFiniteRayRepresentative K n i)

theorem sourceKPFiniteRay_principal (q : Kˣ) :
    _root_.IdeleGroup.finiteEquivFiniteAdeleUnits (_root_.IdeleGroup.principalIdele K q).2 =
      FiniteAdeleRing.unitEmbedding (𝓞 K) K q :=
  congrArg (sourceKPIdeleFiniteUnit K) (sourceKPCFTIdeleEquiv_principal K q)

theorem sourceKPFiniteRayAdele_decomposition (n : RayClass.FiniteModulus K) (a : (𝔸ᶠ[K])ˣ) :
    ∃ q : Kˣ, ∃ u : RayClass.finiteCongruenceSubgroup n,
      a = FiniteAdeleRing.unitEmbedding (𝓞 K) K q *
        sourceKPFiniteRayAdeleRepresentative K n (sourceKPFiniteRayAdeleLabel K n a) *
          _root_.IdeleGroup.finiteEquivFiniteAdeleUnits u.val := by
  let e := _root_.IdeleGroup.finiteEquivFiniteAdeleUnits (K := K)
  obtain ⟨q,u,hu⟩ := sourceKPFiniteRay_decomposition K n (e.symm a)
  refine ⟨q,u,?_⟩
  have h := congrArg e hu
  dsimp only [e] at h
  simpa only [MulEquiv.apply_symm_apply, map_mul, sourceKPFiniteRay_principal,
    sourceKPFiniteRayAdeleLabel, sourceKPFiniteRayAdeleRepresentative] using h

end
end ArtinMatthews
