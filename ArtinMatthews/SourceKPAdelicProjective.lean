module

public import ArtinMatthews.SourceKPProjectiveProduct
public import ArtinMatthews.SourceKPFiniteAdeleRationalSplit
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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


set_option backward.privateInPublic true
@[expose] public section

/-! The actual algebraic cubic cover over PGL2 of the adele ring,
using the finite cover and the split infinite-place group. Its kernel
and rational splitting are the proved ones on the actual factors. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

abbrev SourceKPAdelicProjective := PGL(2, InfiniteAdeleRing K) × SourceKPFiniteAdeleProjective K hζ

def sourceKPAdelicProjectiveProductEquiv :
    PGL(2, 𝔸[K]) ≃* PGL(2, InfiniteAdeleRing K) × PGL(2, 𝔸ᶠ[K]) :=
  sourceKPProjectiveProductEquiv (InfiniteAdeleRing K) 𝔸ᶠ[K]

def sourceKPAdelicProjectiveProjection : SourceKPAdelicProjective K hζ →* PGL(2, 𝔸[K]) :=
  (sourceKPAdelicProjectiveProductEquiv K).symm.toMonoidHom.comp
    (MonoidHom.prodMap (MonoidHom.id _) (sourceKPFiniteAdeleProjectiveProjection K hζ))

theorem sourceKPAdelicProjectiveProjection_product (g : SourceKPAdelicProjective K hζ) :
    sourceKPAdelicProjectiveProductEquiv K (sourceKPAdelicProjectiveProjection K hζ g) =
      (g.1, sourceKPFiniteAdeleProjectiveProjection K hζ g.2) :=
  (sourceKPAdelicProjectiveProductEquiv K).apply_symm_apply _

def sourceKPAdelicProjectiveCenter : rootsOfUnity 3 K →* SourceKPAdelicProjective K hζ :=
  (1 : rootsOfUnity 3 K →* PGL(2, InfiniteAdeleRing K)).prod (sourceKPFiniteAdeleProjectiveCenter K hζ)

theorem sourceKPAdelicProjectiveCenter_injective : Function.Injective (sourceKPAdelicProjectiveCenter K hζ) := by
  intro z w h
  exact sourceKPFiniteAdeleProjectiveCenter_injective K hζ (congrArg Prod.snd h)

theorem sourceKPAdelicProjectiveCenter_commute (z : rootsOfUnity 3 K) (g : SourceKPAdelicProjective K hζ) :
    Commute (sourceKPAdelicProjectiveCenter K hζ z) g := by
  apply Prod.ext
  · change 1 * g.1 = g.1 * 1
    rw [one_mul, mul_one]
  · exact (sourceKPFiniteAdeleProjectiveCenter_commute K hζ z g.2).eq

theorem sourceKPAdelicProjectiveProjection_surjective : Function.Surjective (sourceKPAdelicProjectiveProjection K hζ) := by
  intro g
  let p := sourceKPAdelicProjectiveProductEquiv K g
  obtain ⟨x, hx⟩ := sourceKPFiniteAdeleProjectiveProjection_surjective K hζ p.2
  refine ⟨(p.1, x), (sourceKPAdelicProjectiveProductEquiv K).injective ?_⟩
  rw [sourceKPAdelicProjectiveProjection_product]
  exact Prod.ext rfl hx

theorem sourceKPAdelicProjective_exact :
    (sourceKPAdelicProjectiveCenter K hζ).range = (sourceKPAdelicProjectiveProjection K hζ).ker := by
  ext g
  constructor
  · rintro ⟨z, rfl⟩
    change sourceKPAdelicProjectiveProjection K hζ (sourceKPAdelicProjectiveCenter K hζ z) = 1
    apply (sourceKPAdelicProjectiveProductEquiv K).injective
    rw [sourceKPAdelicProjectiveProjection_product, map_one]
    exact Prod.ext rfl ((sourceKPFiniteAdeleProjective_exact K hζ).le ⟨z, rfl⟩)
  · intro hg
    change sourceKPAdelicProjectiveProjection K hζ g = 1 at hg
    have h := congrArg (sourceKPAdelicProjectiveProductEquiv K) hg
    rw [sourceKPAdelicProjectiveProjection_product, map_one] at h
    have hi : g.1 = 1 := congrArg Prod.fst h
    have hf : g.2 ∈ (sourceKPFiniteAdeleProjectiveProjection K hζ).ker := congrArg Prod.snd h
    rw [← sourceKPFiniteAdeleProjective_exact K hζ] at hf
    obtain ⟨z, hz⟩ := hf
    exact ⟨z, Prod.ext hi.symm hz⟩

def sourceKPAdelicProjectiveRationalLift : PGL(2, K) →* SourceKPAdelicProjective K hζ :=
  (ProjGenLinGroup.map (algebraMap K (InfiniteAdeleRing K))).prod (sourceKPFiniteAdeleProjectiveRationalLift K hζ)

theorem sourceKPAdelicProjectiveRationalLift_projection (g : PGL(2, K)) :
    sourceKPAdelicProjectiveProjection K hζ (sourceKPAdelicProjectiveRationalLift K hζ g) =
      ProjGenLinGroup.map (algebraMap K 𝔸[K]) g := by
  apply (sourceKPAdelicProjectiveProductEquiv K).injective
  rw [sourceKPAdelicProjectiveProjection_product]
  change (ProjGenLinGroup.map (algebraMap K (InfiniteAdeleRing K)) g,
    sourceKPFiniteAdeleProjectiveProjection K hζ (sourceKPFiniteAdeleProjectiveRationalLift K hζ g)) = _
  rw [sourceKPFiniteAdeleProjectiveRationalLift_projection]
  induction g using ProjGenLinGroup.induction_on with
  | mk g => rfl

end
end ArtinMatthews
